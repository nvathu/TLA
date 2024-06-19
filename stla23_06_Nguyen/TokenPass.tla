---- MODULE TokenPass ----
EXTENDS Naturals, FiniteSets
VARIABLE wires,accessed

CONSTANT N

TypeInvariant == /\ accessed \in 0..N-1
                 /\ \A i \in 0..N-1 : wires[i] \in BOOLEAN 
----
Init == 
        /\ wires = [i \in 0..N-1 |-> FALSE]
        /\ accessed = 0

Relay(i) ==  
    /\ accessed' = i
    /\ wires' = [wires EXCEPT ![i] = TRUE]

Next == \E i \in 0..N-1 :
         /\ wires[i] # wires[(i - 1 + N) % N]   
         /\ (i = 0 /\ wires[0] = wires[N - 1])   
         => 
         /\ Relay((i + 1) % N)
         /\ accessed' = (i+1) % N

Liveness == []<>(\A i \in 0..N-1 : ~wires[i] => \E j \in 0..N-1 : wires[j])

RefinementMapping == 
    /\ TypeInvariant
    /\ accessed = Cardinality({i \in 0..N-1 : wires[i]})

Safety == \A i, j \in 0..N-1 : i # j => ~ (wires[i] /\ wires[j])

Spec == Init /\ [][Next]_<<wires, accessed>> /\ Liveness
======

THEOREM Spec => []TypeInvariant /\ []Safety