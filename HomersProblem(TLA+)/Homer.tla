------------------------------- MODULE Homer -------------------------------

\* -> baby
\* <- NONE
\* -> poison
\* <- baby
\* -> dog
\* <- NONE
\* -> baby

EXTENDS Integers, FiniteSets

CONSTANTS baby, dog, poison

Passenger == {baby, dog, poison}

VARIABLES destination, boatAtDestination, start
\*  destination          passengers  who have reached the destination
\*  boatAtDestination    is the boat at the destination? 
                           
Init == /\ boatAtDestination = FALSE
        /\ destination = {}
        /\ start = Passenger
 
TypeOk == /\ boatAtDestination \in {TRUE, FALSE}
          /\ destination \in SUBSET (Passenger)
          /\ start \in SUBSET(Passenger)


Forth(P) == /\ boatAtDestination = FALSE
            /\ IF start # {}
               THEN /\ destination' = destination \cup {P}
                    /\ boatAtDestination' = TRUE
                    /\ start' = start \ {P}
                ELSE UNCHANGED << start, destination >>


Back(P) ==  /\ boatAtDestination = TRUE
            /\ IF start # {}
               THEN /\ destination' = destination \ {P}
                    /\ boatAtDestination' = FALSE
                    /\ start' = start \cup {P}
                ELSE UNCHANGED << start, destination >>


Next == 
        IF destination = Passenger
        THEN UNCHANGED << start, destination >> /\  boatAtDestination' = TRUE
        ELSE 
        \/ \E P \in Passenger : Forth(P)
        \/ \E P \in Passenger : Back(P)
        


Safe == 
        \/ ({baby, dog} \in SUBSET (start) /\ ~ boatAtDestination = TRUE) 
        \/ ({baby, dog} \in SUBSET (destination) /\ ~ boatAtDestination = FALSE) 
        \/ ({baby, poison} \in SUBSET (start) /\ ~ boatAtDestination = TRUE) 
        \/ ({baby, poison} \in SUBSET (destination) /\ ~ boatAtDestination = FALSE) 
\* check the baby is never alone with the dog or the poison






=============================================================================
\* Modification History
\* Last modified Thu Apr 08 18:52:22 EDT 2021 by Shesan
\* Created Sun Apr 04 11:24:52 EDT 2021 by Shesan
