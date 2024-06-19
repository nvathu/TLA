---- MODULE ResettableClock_correct ----
EXTENDS Naturals
VARIABLE  hr, chan
HR == INSTANCE HourClock
Chan == INSTANCE  Channel WITH  Data <- (1..12)
TypeInvariant == HC!HCini /\ Chan!TypeInvariant
-------
Init == HC!HCini /\ Chan!Init
Tick == /\ HC!Hcnxt
        /\ UNCHANGED chan
Send() == /\ \E v \in (1..12): Chan!Send(v)
        /\ UNCHANGED hr
Send2(v) == /\  Chan!Send(v)
            /\ UNCHANGED hr
Reset == /\ Chan !Rcv
         /\ hr' = chan.v 

Next == Tick \/ Send \/ Reset
Spec == Init /\ [][Next]_<<chan,hr>>


====