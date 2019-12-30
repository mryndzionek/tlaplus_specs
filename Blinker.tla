------------------------------ MODULE Blinker ------------------------------
EXTENDS Integers, Sequences

(***************************************************************************)
(* BC is a sequence of blinker configurations - in this case just          *)
(* a natural number signifying the blink period in some time unit          *)
(***************************************************************************)
CONSTANT BC
VARIABLES bState

ASSUME /\ BC \in Seq(Nat)

vars == bState

States == {"Active_Off", "Active_On"}
Blinker == [timer : Nat, state : States]

TypeOK == /\ bState \in [DOMAIN BC -> Blinker]

Init ==
    /\ bState = [n \in DOMAIN BC |-> [timer |-> BC[n],
                                      state |-> "Active_Off"]
                ]
                                
Transition(n) == /\ bState[n].timer = 0
                 /\ bState[n].state = "Active_Off"
                 /\ bState' = [bState EXCEPT ![n].timer = BC[n],
                                             ![n].state = "Active_On"]
              \/
                 /\ bState[n].timer = 0
                 /\ bState[n].state = "Active_On"
                 /\ bState' = [bState EXCEPT ![n].timer = BC[n],
                                             ![n].state = "Active_Off"]
             
Tick == /\ \A n \in DOMAIN BC : bState[n].timer > 0
        /\ bState' = [n \in DOMAIN BC |-> [timer |-> bState[n].timer - 1,
                                           state |-> bState[n].state]]

Next == Tick \/ \E n \in DOMAIN BC : Transition(n)

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

LEDsWillTurnOn ==
    \A n \in DOMAIN BC :
        (bState[n].state = "Active_Off") ~> (bState[n].state = "Active_On")
    
LEDsWillTurnOff ==
    \A n \in DOMAIN BC :
        (bState[n].state = "Active_On")  ~> (bState[n].state = "Active_Off")

=============================================================================
