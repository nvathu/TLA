------------------------------ MODULE Sum ------------------------------
EXTENDS Naturals, Sequences
CONSTANT Data



-----
Init == TRUE

Sum(a, b) == a + b

\* Sum(s) == IF s = <<>> THEN 0 ELSE Head(s) + Sum(Tail(s))

RECURSIVE CalSum(_)

CalSum(s) == IF s = {} THEN 0 
            ELSE LET h == Head(s)
                     t ==Tail(s)
                 IN h + CalSum(t)


Next == \E s \in Data : CalSum(s)

Spec == Init /\ [][Next]_Data
=============================================================================