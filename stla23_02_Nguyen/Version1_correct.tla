----------------- MODULE Version1_correct ----
VARIABLE    hr, chan
HC == INSTANCE HourClock
Chan == INSTANCE  Channel WITH  Data <- (1..12)
TypeInvariant ==  HC!HCini /\ Chan!TypeInvariant
-----------------
Init == HC!HCini /\ Chan!Init
Send == /\ Chan(Send(hr))
        /\ UNCHANGED hr

Tick == /\ HC!HCnxt
        /\ UNCHANGED chan

Rcv == /\ Chan!Rcv
       /\ UNCHANGED hr
Next == Tick\/ Rcv\/ Send 
Spec == Init /\ [][Next]_<<chan,hr>>
-------------------
THEOREM 
Channel_Spec == Chan!Spec




====