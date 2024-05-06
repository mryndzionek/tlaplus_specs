---- MODULE Scheduler ----
(***************************************************************************)
(*            A specification of a simple rate-monotonic scheduler         *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

VARIABLE tasks, scheduler

vars == <<tasks, scheduler>>

TasksCfg == <<[prio |-> 2, p |-> 17, et |-> 3],
              [prio |-> 1, p |-> 21, et |-> 5],
              [prio |-> 3, p |-> 9,  et |-> 2]>>

N == Len(TasksCfg)
NoTask == CHOOSE v : v \notin 1..N

ASSUME DOMAIN TasksCfg = 1..N
                        
TypeOK == /\ tasks \in [1..N -> [s : {"idle", "running", "pending"},
                                 tmr : Int,
                                 tmR : Int,
                                 hasRun : BOOLEAN]]
          /\ scheduler \in [uid : 1..N \cup {NoTask}]

Init == /\ tasks = [uid \in 1..N |-> [s |-> "pending", 
                                      tmr |-> TasksCfg[uid].et - 1,
                                      tmR |-> 0, hasRun |-> TRUE]]
        /\ scheduler = [uid |-> NoTask]
        
Update(uid) == /\ ~tasks[uid].hasRun
               /\ \/ /\ tasks[uid].s = "idle"
                     /\   \/ /\ tasks[uid].tmr = 0
                             /\ tasks' = [tasks EXCEPT ![uid].s = "pending",
                                                       ![uid].tmR = 0,
                                                       ![uid].tmr = TasksCfg[uid].et - 1,
                                                       ![uid].hasRun = TRUE]
                          \/ /\ tasks[uid].tmr > 0
                             /\ tasks' = [tasks EXCEPT ![uid].tmr = @ - 1,
                                                       ![uid].hasRun = TRUE]
                  \/ /\ tasks[uid].s = "running"
                     /\   \/ /\ tasks[uid].tmr = 0
                             /\ tasks' = [tasks EXCEPT ![uid].s = "idle",
                                                       ![uid].tmR = 0,
                                                       ![uid].tmr = TasksCfg[uid].p -
                                                                    tasks[uid].tmR - 2,
                                                       ![uid].hasRun = TRUE]
                          \/ /\ tasks[uid].tmr > 0
                             /\ tasks' = [tasks EXCEPT ![uid].tmr = @ - 1,
                                               ![uid].tmR = @ + 1,
                                               ![uid].hasRun = TRUE]
                  \/ /\ tasks[uid].s = "pending"
                     /\ tasks' = [tasks EXCEPT ![uid].tmR = @ + 1,
                                               ![uid].hasRun = TRUE]
               /\ UNCHANGED scheduler

MaxPendingUID == LET Max(S) == CHOOSE x \in S : \A y \in S : TasksCfg[x].prio >= TasksCfg[y].prio
                     C == {uid \in 1..N : tasks[uid].s = "pending"}
                     MaxP == Max(C)
                 IN IF C = {} THEN NoTask ELSE MaxP

SetMaxPendingAsRunning == tasks' = [uid \in 1..N |-> 
                            [tasks[uid] EXCEPT
                                         !.hasRun = FALSE,
                                         !.s = IF uid = MaxPendingUID THEN "running"
                                               ELSE IF /\ uid = scheduler.uid
                                                       /\ tasks[uid].s = "running"
                                                    THEN "pending"
                                                    ELSE tasks[uid].s]]

Tick == /\ \A uid \in 1..N : tasks[uid].hasRun
        /\ LET CurrUID == IF scheduler.uid = NoTask THEN NoTask
                          ELSE IF tasks[scheduler.uid].s = "idle" THEN NoTask
                          ELSE scheduler.uid
           IN IF CurrUID = NoTask
              THEN IF MaxPendingUID = NoTask
                   THEN /\ tasks' = [uid \in 1..N |-> [tasks[uid] EXCEPT !.hasRun = FALSE]]
                        /\ scheduler' = [uid |-> NoTask]
                   ELSE /\ SetMaxPendingAsRunning
                        /\ scheduler' = [uid |-> MaxPendingUID]
              ELSE IF MaxPendingUID = NoTask
                   THEN /\ tasks' = [uid \in 1..N |-> [tasks[uid] EXCEPT !.hasRun = FALSE]]
                        /\ scheduler' = [uid |-> CurrUID]
                   ELSE IF TasksCfg[MaxPendingUID].prio > TasksCfg[CurrUID].prio
                        THEN /\ SetMaxPendingAsRunning
                             /\ scheduler' = [uid |-> MaxPendingUID]
                        ELSE /\ tasks' = [uid \in 1..N |-> [tasks[uid] EXCEPT !.hasRun = FALSE]]
                             /\ scheduler' = [uid |-> CurrUID]


Next == \E uid \in 1..N : Update(uid) \/ Tick
        
Spec == Init /\ [][Next]_vars

NoMissingDeadlines == \A uid \in 1..N : tasks[uid].tmR + 2 < TasksCfg[uid].p
          
====
