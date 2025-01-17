---- MODULE spec ----
EXTENDS TLC

VARIABLES start, end

vars == <<start, end>>

Farmer == "Farmer"
Wolf == "Wolf"
Goat == "Goat"
Cabbage == "Cabbage"

Items == {Farmer, Wolf, Goat, Cabbage}

Init ==
    /\ start = Items
    /\ end = {}

TypeOk ==
    /\ start \subseteq Items
    /\ end \subseteq Items

MoveToEnd ==
    /\ Farmer \in start
    /\ \E item \in start:
        /\ start' = start \ {Farmer, item}
        /\ end' = end \union {Farmer, item}
        /\ Farmer \notin start' => ~({Wolf, Goat} \subseteq start') /\ ~({Goat, Cabbage} \subseteq start')
        /\ Farmer \notin end' => ~({Wolf, Goat} \subseteq end') /\ ~({Goat, Cabbage} \subseteq end')

MoveToStart ==
    /\ Farmer \in end
    /\ \E item \in end:
        /\ end' = end \ {Farmer, item}
        /\ start' = start \union {Farmer, item}
        /\ Farmer \notin start' => ~({Wolf, Goat} \subseteq start') /\ ~({Goat, Cabbage} \subseteq start')
        /\ Farmer \notin end' => ~({Wolf, Goat} \subseteq end') /\ ~({Goat, Cabbage} \subseteq end')

Next ==
    \/ MoveToEnd
    \/ MoveToStart

Spec == Init /\ [][Next]_vars
----
NotAllItemsOnEnd ==
    end /= Items

GoatIsNeverAloneWithCabbage ==
    /\ {Goat, Cabbage} \subseteq start => Farmer \in start
    /\ {Goat, Cabbage} \subseteq end  => Farmer \in end

WolfIsNeverAloneWithGoat  ==
    /\ {Wolf, Goat} \subseteq start => Farmer \in start
    /\ {Wolf, Goat} \subseteq end  => Farmer \in end
====