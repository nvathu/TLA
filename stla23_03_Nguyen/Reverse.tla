------------- MODULE Reverse---------------
EXTENDS Sequences, Naturals

VARIABLES s
--------------------
Init == s \in {<<1, 2, 3, 2>>, <<>>}
Next == s' = IF Len(s) <= 1 THEN s ELSE  <<s[Len(s)]..s[1]>>
Spec == Init /\ [][Next]_s

=============================================================================