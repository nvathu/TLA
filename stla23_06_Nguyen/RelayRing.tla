--------------------- MODULE RelayRing ---------------------
EXTENDS Naturals
VARIABLE accessed
CONSTANT N

TypeInvariant == accessed \in 0..N-1
------------------------------------------------------------
Init == TypeInvariant

Relay(i) == accessed' = i

Next ==  Relay((accessed + 1) % N)

Spec == Init /\ [][Next]_<<accessed>>
------------------------------------------------------------
THEOREM Spec => []TypeInvariant
============================================================
