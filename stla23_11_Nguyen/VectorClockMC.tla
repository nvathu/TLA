---- MODULE VectorClockMC ----
EXTENDS VectorClock

Events == \A  i \in Procs: SendEvent(i) \union ReceiveEvent(i) 

HappenedBefore(A,B) == 
  IF A = B
  THEN TRUE
  ELSE IF \E i \in Procs : A = SendEvent(i) /\ B = ReceiveEvent(i)
       THEN TRUE
       ELSE \E C \in Events :
              /\ HappenedBefore(A, C)
              /\ HappenedBefore(C, B)


InitMC == Init

MC == InitMC /\ [][Next]_<<msg, vc>>
=========