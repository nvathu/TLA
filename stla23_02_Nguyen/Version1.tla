---------------------- MODULE Version1 ------------------------
EXTENDS Channel, HourClock, Naturals

TypeInvariantV1  ==  TypeInvariant /\ HCini
----- 
InitV1 == /\ TypeInvariantV1
          /\ Init

TickSend == /\ HCnxt
            /\ Send(hr)

TickReceive == /\ Rcv
               /\ TypeInvariant
               /\ HCnxt

Nextv1 == TickSend \/ TickReceive

SpecClockV1 == InitV1 /\ [][Nextv1]_chan
-----
THEOREM SpecClockV1 => []TypeInvariantV1
=====