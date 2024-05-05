---- MODULE Watchdog ----
(***************************************************************************)
(* A specification of a simple software watchdog multiplexing system.      *)
(*                                                                         *)
(* On many (most) MCUs a hardware watchdog has only one time interval.     *)
(* However in most cases there are multiple software tasks/components      *)
(* with different timing constraints. Solution to this is a separate       *)
(* software component mediating between the hardware watchdog and the      *)
(* other software components. The software watchdog maintains a set of its *)
(* own software timers. Each software component periodically feeds the     *)
(* software watchdog which results in the appropriate timer being reset.   *)
(* The software watchdog feeds the hardware watchdog with its own software *)
(* timer-set update rate. This results in an optimal reaction to any       *)
(* software failure.                                                       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS N, T
VARIABLE components, watchdog

vars == <<components, watchdog>>

(***************************************************************************)
(* A software component is modeled as a periodic state machine driven by   *)
(* a timer and can crash and halt at any time. The 'ready' flag is used to *)
(* model synchronicity between the component and the software watchdog.    *)
(***************************************************************************)
TypeOK == /\ components \in [1..N -> [timer : 0..T,
                                      timeout : 0..T,
                                      ready : BOOLEAN,
                                      crashed : BOOLEAN]]
          /\ watchdog \in [1..N -> [timer : 0..T + 1]]
          
Init == /\ components \in [1..N -> {[timer |-> x, 
                                     timeout |-> x,
                                     ready |-> TRUE,
                                     crashed |-> FALSE] : x \in {T}}]
        /\ watchdog = [uid \in 1..N |-> [timer |-> components[uid].timeout + 1]]

RunOne(c) == IF c.timer > 0
                THEN [c EXCEPT !.timer = @ - 1]
                ELSE [c EXCEPT !.timer = c.timeout]
                
WatchdogUpdate(uid) == IF watchdog[uid].timer > 0
                       THEN watchdog[uid].timer - 1
                       ELSE 0

WatchdogFeed(uid) == IF components[uid].timer = 0
                     THEN components[uid].timeout + 1
                     ELSE WatchdogUpdate(uid)

Run(uid) == 
    /\ \A id \in 1..N : watchdog[id].timer > 0
    /\ components[uid].ready
    /\ IF components[uid].crashed
        THEN /\ components' = [components EXCEPT ![uid].ready = FALSE]
             /\ watchdog' = [watchdog EXCEPT ![uid].timer = WatchdogUpdate(uid)]
        ELSE /\ components' = [components EXCEPT ![uid] = RunOne(components[uid]),
                                                 ![uid].ready = FALSE]
             /\ watchdog' = [watchdog EXCEPT ![uid].timer = WatchdogFeed(uid)]

Crash(uid) == /\ ~components[uid].crashed
              /\ components[uid].ready
              /\ components' = [components EXCEPT ![uid].crashed = TRUE]
              /\ UNCHANGED watchdog

Reset == /\ \E uid \in 1..N : watchdog[uid].timer = 0
         /\ watchdog' = [uid \in 1..N |-> [timer |-> components[uid].timeout + 1]]
         /\ components' = [uid \in 1..N |-> [timer |-> components[uid].timeout,
                                             timeout |-> components[uid].timeout,
                                             ready |-> TRUE,
                                             crashed |-> FALSE]]

Tick == /\ \A uid \in 1..N : ~components[uid].ready
        /\ UNCHANGED watchdog
        /\ components' = [uid \in 1..N |-> [components[uid] EXCEPT !.ready = TRUE]]

Next == (\E uid \in 1..N : Run(uid) \/ Crash(uid)) \/ Tick \/ Reset
        
Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Make sure a crashed component leads to a global system reset            *)
(***************************************************************************)
AlwaysReset == (\E uid \in 1..N: components[uid].crashed) ~> 
             <>(\A uid \in 1..N: ~components[uid].crashed)

====