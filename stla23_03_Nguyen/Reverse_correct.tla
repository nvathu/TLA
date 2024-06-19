---- MODULE Reverse_correct ----
EXTENDS Naturals,Sequences
VARIABLE  s0,steps,sum 
------
Sum [s \in Seq(Nat)]== IF Len(s)=0 THEN 0 ELSE Sum[Tai(s)+Head(s)]
Init == <<1,2,3,4>> /\ sum =Sum[s0] /\ steps =0

Reverse(s) == [i \in DOMAIN  s |->[Len(s)-i + 1]]
Next == s0' = Reverse(s0) /\ steps' =   steps+1
Spec == Init /\ []Next_<<>>
DebugInvariant == steps <= 4


====