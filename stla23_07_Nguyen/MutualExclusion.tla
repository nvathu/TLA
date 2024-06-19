-------------- MODULE MutualExclusion --------------
EXTENDS Naturals, Sequences, Semaphores

CONSTANT N

VARIABLE pc, semaphores

Init ==
    /\ pc = [i \in 1..N |-> 2]   
    /\ semaphores = [i \in 1..N |-> 1]  


Process(i) ==
    /\ pc[i] = 2 /\ pc' = [pc EXCEPT ![i] = 3]  
    /\ P(semaphores[i])  
    /\ pc' = [pc EXCEPT ![i] = 4]  

    /\ pc[i] = 4 /\ pc' = [pc EXCEPT ![i] = 5] 
    /\ V(semaphores[i])  
    /\ pc' = [pc EXCEPT ![i] = 2]  

Next ==
    \E i \in 1..N: Process(i)  

MutExInvariant ==
    \A i, j \in 1..N: i # j => pc[i] = 2 \/ pc[j] = 2
------------
vars == <<pc, semaphores>> 

ENABLED_condition == \E i \in 1..N:  pc[i] = 3 /\ pc[i] = 4

(*Liveness ==
    \A i \in 1..N: WF_vars(ENABLED_condition,vars)*)

Liveness ==
    \A i \in 1..N: WF_vars(ENABLED_condition)


Spec == Init /\ [][Next]_<<pc, semaphores>> /\ Liveness

===============================================