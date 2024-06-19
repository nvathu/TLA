-------- MODULE TwoPhaseCommit ----------
EXTENDS Integers

VARIABLES coordinatorState, participantStates

CONSTANT Participants 

vars == <<coordinatorState, participantStates>>

Init == 
    /\ coordinatorState = "INIT"
    /\ participantStates = [p \in Participants |-> "INIT"]

VotingPhase(p) == 
    /\ coordinatorState = "VOTING"
    /\ participantStates[p] = "INIT"
    /\ participantStates' = [participantStates EXCEPT ![p] = "READY"]
    /\ \/ \A q \in Participants : participantStates[q] \in {"READY", "VOTED_YES", "VOTED_NO"}
       \/ coordinatorState' = "DECIDING"

DecisionPhase == 
    /\ coordinatorState = "DECIDING"
    /\ \/ \A p \in Participants : participantStates[p] = "VOTED_YES"
          /\ coordinatorState' = "COMMIT"
       \/ \A p \in Participants : participantStates[p] = "VOTED_NO"
          /\ coordinatorState' = "ABORT"
Fairness ==
    /\ SF_vars(\A p \in Participants : VotingPhase(p))
    /\ SF_vars(DecisionPhase)

Next ==  \/ coordinatorState' = "VOTING" /\ \E p \in Participants : VotingPhase(p)
         \/ IF coordinatorState = "VOTING" 
            THEN DecisionPhase
            ELSE /\ coordinatorState' = coordinatorState
                 /\ participantStates' = participantStates
    

Spec == Init /\ [][Next]_<<coordinatorState, participantStates>>  /\ Fairness

==================