------------------------------ MODULE Count ------------------------------
EXTENDS  Sequences,Naturals
VARIABLE r
----------------------

Init == r  = [count |-> 0] /\ r.count \in (1..10)
\* sometime my code go into a infinity loop, please carefully if you run it
(*
AF(r) ==   IF "count" \in DOMAIN r 
           THEN [r EXCEPT !.count = r.count + 1] 
           ELSE [count |-> 0]
*)

Next == /\ r'= IF "count" \in DOMAIN r 
           THEN [r EXCEPT !.count = @ + 1] 
           ELSE [count |-> 0]

Spec == Init /\ [][Next]_<<r>>

=============================================================================