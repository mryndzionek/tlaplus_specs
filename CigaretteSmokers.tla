-------------------------- MODULE CigaretteSmokers --------------------------
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ing, Offers
VARIABLE smokers, dealer

(***************************************************************************)
(* 'Ing' is a set of ingredients, originally {matches, paper, tobacco}     *)
(* 'Offers' is a subset of subsets of ingredients, each missing just one   *)
(* ingriedent                                                              *)
(***************************************************************************)
ASSUME /\ Offers \subseteq (SUBSET Ing)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ing) - 1

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or an empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ing -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}
          
vars == <<smokers, dealer>>

Init == /\ smokers = [r \in Ing |-> [smoking |-> FALSE]]
        /\ dealer \in Offers
        
startSmoking == /\ dealer /= {}
                /\ smokers' = [r \in Ing |-> [smoking |-> {r} \cup dealer = Ing]]
                /\ dealer' = {}
                
stopSmoking == /\ dealer = {}
               /\ LET r == CHOOSE r \in Ing : smokers[r].smoking
                  IN smokers' = [smokers EXCEPT ![r].smoking = FALSE] 
               /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ing : smokers[r].smoking}) <= 1
=============================================================================
