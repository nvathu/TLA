---- MODULE VectorClock ----
EXTENDS Integers, Sequences

CONSTANT N

ASSUME N \in Nat \ {0, 1}

Procs == 1..N

VARIABLE msg, vc

msgInit == [j \in Procs |-> [k \in Procs |-> <<>>]]
vcInit == [j \in Procs |-> 0]

PairMax(V1, V2) == [x \in Procs |-> IF V1[x] > V2[x] THEN V1[x] ELSE V2[x]]

SendEvent(self) == 
  /\ vc[self] < N
  /\ vc' = [vc EXCEPT ![self] = vc[self] + 1]
  /\ msg' = [msg EXCEPT ![self] = [k \in Procs |-> vc']]

ReceiveEvent(self) == 
  /\ \E k \in Procs \ {self} :
       /\ vc' = PairMax(vc, msg[k][self])
       /\ vc'[self] = vc'[self] + 1
       /\ msg' = [msg EXCEPT ![k][self] = vc']

Next == \E self \in Procs :
  \/ SendEvent(self)
  \/ ReceiveEvent(self)

Init == /\ msg = msgInit
        /\ vc = vcInit

Spec == Init /\ [][Next]_<<msg, vc>> 

=============