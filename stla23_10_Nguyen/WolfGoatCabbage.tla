----------- MODULE WolfGoatCabbage -----------
VARIABLES farmer, wolf, goat, cabbage
CONSTANT  Side 

Check ==  {wolf, goat, cabbage, farmer} \in Side

InvariantFinnish == /\ farmer = "right"
                    /\ goat = "right"
                    /\ wolf = "right"
                    /\ cabbage = "right"



Safe (s) ==
    /\ \E side \in Side: (wolf = side) => (goat /= side)
    /\ \E side \in Side: (cabbage = side) => (goat /= side)  

SafeNow == Safe({wolf, goat, cabbage})
SafeNext == Safe({wolf', goat', cabbage'})
TotalSafe == SafeNow /\ SafeNext

Init == /\ farmer = "left"
        /\ wolf = "left"
        /\ goat = "left"
        /\ cabbage = "left"

SafeCrossing == /\ Init
                /\ \/ (/\ farmer' = "right"
                      /\ cabbage' = "right"
                      /\ wolf' = wolf
                      /\ goat' = goat)
                   \/ (/\ farmer' = "right"
                      /\ cabbage' = cabbage 
                      /\ wolf' = "right" 
                      /\ goat' = goat)
                   \/ (/\ farmer' = "right"
                       /\ cabbage' = cabbage 
                      /\ wolf' = wolf 
                      /\ goat' = "right")
                /\ TotalSafe
GoWithNone == /\ \/ /\ farmer = "left"
                    /\ farmer' = "right"
                    /\ cabbage' = cabbage
                    /\ wolf' = wolf
                    /\ goat' = goat
                 \/ /\ farmer = "right"
                    /\ farmer' = "left"
                    /\ cabbage' = cabbage
                    /\ wolf' = wolf
                    /\ goat' = goat
              /\ TotalSafe
Next == \/ SafeCrossing 
        \/ GoWithNone

Spec == Init /\ [][Next]_<<farmer, wolf, goat, cabbage>>


==================