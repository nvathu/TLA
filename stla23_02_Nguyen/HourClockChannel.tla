---------------------- MODULE HourClockChannel ------------------------
EXTENDS Naturals
VARIABLE chan 

TypeInvariant == chan \in [val : (1..12),  rdy : {0, 1},  ack : {0, 1}]
-----------------------------------------------------------------------
Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy 

Send == /\ chan.rdy = chan.ack
        /\ chan' = [chan EXCEPT 
                    !.val = IF chan.val = 12 THEN 1 ELSE chan.val + 1, 
                    !.rdy = 1 - chan.rdy]

Rcv ==  /\ chan.rdy # chan.ack
        /\ chan' = [chan EXCEPT !.ack = 1 - chan.ack]

Next == Send \/ Rcv

Spec == Init /\ [][Next]_chan
-----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=======================================================================
