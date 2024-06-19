---------------------- MODULE ResettableClock ------------------------
EXTENDS Channel, HourClock,Naturals

TypeInvariant2 == TypeInvariant /\ HCini
------
Init2 == /\ Init
         /\ TypeInvariant2
\* User send data value (define in channel),take this data save in to hr
UserSend == /\ chan.rdy = chan.ack
            /\ chan' = [chan EXCEPT !.val = Data, !.rdy = 1 - chan.rdy]
            /\ hr' = Data

\* Receive and handle clock again 
Reset == /\ Rcv
         /\ chan' = [chan EXCEPT !.ack = 1 - chan.ack]
         /\ hr' = IF hr # 12 THEN hr + 1 ELSE 1


Next2 == UserSend \/ Reset


Spec2 == Init2 /\ [][Next2]_chan

-----
THEOREM Spec2 => []TypeInvariant2
==============================================================================