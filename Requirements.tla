---------------------------- MODULE Requirements ----------------------------
EXTENDS Integers

VARIABLES inputs, output

(***************************************************************************)
(* We have two buttons - A and B - and an indicator light. Spec like this  *)
(* can help with disambiguating written requirements in situations where   *)
(* multiple requirements concern same resource. In this case requirements  *)
(* say only what needs to be done if one of the button is pressed or not   *)
(* totally ignoring the situation where both are pressed                   *)
(***************************************************************************)
Inputs == SUBSET {"a_button_pressed", "b_button_pressed"}
Output == {"off", "red", "green", "yellow"}

TypeOK == /\ inputs \in Inputs
          /\ output \in Output

(***************************************************************************)
(* Initially indicator light is off and buttons can pushed or not          *)
(***************************************************************************)
Init == /\ inputs \in Inputs
        /\ output = "off"
        
(***************************************************************************)
(* First requirement says that we signal with green light the fact that    *)
(* button A is pushed. If it's not then the light should be yellow         *)
(***************************************************************************)
Requirement1 == /\ IF "a_button_pressed" \in inputs THEN output' = "green"
                   ELSE output' = "yellow"
                /\ UNCHANGED <<inputs>>

(***************************************************************************)
(* Second requirement says that we signal with red light the fact that     *)
(* button B is pushed. If it's not then the light should be yellow         *)
(***************************************************************************)
Requirement2 == /\ IF "b_button_pressed" \in inputs THEN output' = "green"
                   ELSE output' = "yellow"
                /\ UNCHANGED <<inputs>>
                  
(***************************************************************************)
(* We want to check all requirements                                       *)
(***************************************************************************)         
Next == Requirement1 \/ Requirement2

=============================================================================
