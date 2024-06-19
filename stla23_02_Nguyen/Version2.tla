---------------------- MODULE Version2 ------------------------
EXTENDS Channel, HourClock

TypeInvariantv2 == TypeInvariant /\ HCini
----
InitV2 == /\ TypeInvariantv2
          /\ HCini
          /\ Init

Receivev2 == /\ Rcv
           /\ TypeInvariant
           /\ HCnxt

Sendv2 == /\ Send(hr)
        /\ UNCHANGED hr

Nextv2 == \/ Sendv2 
          \/ Receivev2

SpecClockV2 == InitV2 /\ [][Nextv2]_chan
----
THEOREM SpecClockV2 => []TypeInvariantv2
====