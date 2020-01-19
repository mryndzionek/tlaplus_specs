-------------------------- MODULE CheckRequirements -------------------------
VARIABLES inputs1, output1
VARIABLES inputs2, output2

vars1 == <<inputs1, output1>>
vars2 == <<inputs2, output2>>

Requirements1 == INSTANCE Requirements
           WITH inputs <- inputs1,
                output <- output1
                
Requirements2 == INSTANCE Requirements
           WITH inputs <- inputs2,
                output <- output2
                
Init == Requirements1!Init /\ Requirements2!Init
Next == Requirements1!Next /\ Requirements2!Next
      
RequirementsNotConflicting == inputs1 = inputs2 => output1 = output2
EndsInSteadyState == <>[][output1 = output2]_<<output1, output2>>

=============================================================================
