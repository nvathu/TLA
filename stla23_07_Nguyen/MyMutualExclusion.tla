-------------- MODULE MyMutualExclusion--------------
EXTENDS Naturals

CONSTANT N

VARIABLE pc, inCriticalSection


Init ==
    /\ pc = [i \in 1..N |-> "NonCritical"]  
    /\ inCriticalSection = FALSE  


Process(i) ==
    /\ pc[i] = "NonCritical" /\ pc' = [pc EXCEPT ![i] = "Waiting"]  
    /\ ~inCriticalSection 
    /\ pc' = [pc EXCEPT ![i] = "InCriticalSection"] 

    /\ pc[i] = "InCriticalSection" /\ pc' = [pc EXCEPT ![i] = "NonCritical"]  
    /\ inCriticalSection' = FALSE  

Next ==
    \E i \in 1..N: Process(i)  


vars == <<pc, inCriticalSection>>

Condition == \A i \in 1..N: pc[i] = "Waiting" /\ ~inCriticalSection

Liveness ==
     WF_vars(Condition)

Spec == Init /\ [][Next]_vars /\ Liveness

===============================================