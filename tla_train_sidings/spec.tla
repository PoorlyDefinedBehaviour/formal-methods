---- MODULE spec ----
EXTENDS TLC

\* https://www.heinbockel.eu/2019/12/08/train-sidings-a-tla-example/

VARIABLES t1, t2, s1, s2, s3, s4, sw1, sw2

vars == <<t1, t2, s1, s2, s3, s4, sw1, sw2>>

Init ==
    /\ t1 = "TRACK1"
    /\ t2 = "TRACK4"
    /\ s1 = "STOP"
    /\ s2 = "STOP"
    /\ s3 = "STOP"
    /\ s4 = "STOP"
    /\ sw1 = "STRAIGHT"
    /\ sw2 = "STRAIGHT"

Positions == {"TRACK1", "TRACK2", "TRACK3", "TRACK4", "SWITCH1", "SWITCH2"}
Signals == {"STOP", "GO"}

TypeOk ==
    /\ t1 \in Positions
    /\ t2 \in Positions
    /\ s1 \in Signals
    /\ s2 \in Signals
    /\ s3 \in Signals
    /\ s4 \in Signals
    /\ sw1 \in {"STRAIGHT", "LEFT"}
    /\ sw2 \in {"STRAIGHT", "RIGHT"}

MoveT1 ==
    /\ \/ /\ t1 = "TRACK1"
          /\ s1 = "GO"
          /\ t1' = "SWITCH1"
          /\ s1' = "STOP"
          /\ UNCHANGED <<s2>>
       \/ /\ t1 = "SWITCH1"
          /\ t1' = "TRACK2"
          /\ UNCHANGED <<s1, s2>>
       \/ /\ t1 = "TRACK2"
          /\ s2 = "GO"
          /\ t1' = "SWITCH2"
          /\ s2' = "STOP"
          /\ UNCHANGED <<s1>>
       \/ /\ t1 = "SWITCH2"
          /\ t1' = "TRACK4"
          /\ UNCHANGED <<s1, s2>>
    /\ UNCHANGED <<t2, s3, s4, sw1, sw2>>

MoveT2 ==
    /\ \/ /\ t2 = "TRACK4"
          /\ s4 = "GO"
          /\ t2' = "SWITCH2"
          /\ s4' = "STOP"
          /\ UNCHANGED <<s3>>
       \/ /\ t2 = "SWITCH2"
          /\ t2' = IF sw2 = "STRAIGHT" THEN "TRACK2" ELSE "TRACK3"
          /\ UNCHANGED <<s3, s4>>
       \/ /\ t2 = "TRACK3"
          /\ s3 = "GO"
          /\ t2' = "SWITCH1"
          /\ s3' = "STOP"
          /\ UNCHANGED <<s4>>
       \/ /\ t2 = "SWITCH1"
          /\ t2' = "TRACK1"
          /\ UNCHANGED <<s3, s4>>
    /\ UNCHANGED <<t1, s1, s2, sw1 ,sw2>>

ChangeS1 ==
    /\ t1 = "TRACK1"
    /\ t2 \notin {"TRACK2", "SWITCH1"}
    /\ sw1 = "STRAIGHT"
    /\ s1' = "GO"
    /\ UNCHANGED <<t1, t2, s2, s3, s4, sw1, sw2>>

ChangeS2 ==
    /\ t1 = "TRACK2"
    /\ t2 \notin {"TRACK4", "SWITCH2"}
    /\ sw2 = "STRAIGHT"
    /\ s2' = "GO"
    /\ UNCHANGED <<t1, t2, s1, s3, s4, sw1, sw2>>

ChangeS3 == /\ t2 = "TRACK3"
            /\ t1 \notin {"TRACK1", "SWITCH1"}
            /\ sw1 = "LEFT"
            /\ s3' = "GO"
            /\ UNCHANGED <<t1, t2, s1, s2, s4, sw1, sw2>>
            
ChangeS4 == /\ t2 = "TRACK4"
            /\ t1 \notin {"TRACK3", "SWITCH2"}
            /\ sw2 = "RIGHT"
            /\ s4' = "GO"
            /\ UNCHANGED <<t1, t2, s1, s2, s3, sw1, sw2>>

ChangeSw1 ==
    /\ s1 = "STOP"
    /\ s3 = "STOP"
    /\ t1 /= "SWITCH1"
    /\ t2 /= "SWITCH1"
    /\ \/ /\ sw1 = "STRAIGHT"
          /\ t2 = "TRACK3"
          /\ t1 /= "TRACK1"
          /\ sw1' = "LEFT"
       \/ /\ sw1 = "LEFT"
          /\ t1 = "TRACK1"
          /\ sw1' = "STRAIGHT"
    /\ UNCHANGED <<t1, t2, s1, s2, s3, s4, sw2>>

ChangeSw2 ==
    /\ s2 = "STOP"
    /\ s4 = "STOP"
    /\ t1 /= "SWITCH2"
    /\ t2 /= "SWITCH2"
    /\ \/ /\ sw2 = "STRAIGHT"
          /\ t2 = "TRACK4"
          /\ sw2' = "RIGHT"
       \/ /\ sw2 = "RIGHT"
          /\ t1 = "TRACK2"
          /\ t2 /= "TRACK4"
          /\ sw2' = "STRAIGHT"
    /\ UNCHANGED <<t1, t2, s1, s2, s3, s4, sw1>>

Next == 
    \/ MoveT1
    \/ MoveT2
    \/ ChangeS1
    \/ ChangeS2
    \/ ChangeS3
    \/ ChangeS4
    \/ ChangeSw1
    \/ ChangeSw2

Fairness ==
    /\ WF_vars(MoveT1)
    /\ WF_vars(MoveT2)
    /\ WF_vars(ChangeS1)
    /\ WF_vars(ChangeS2)
    /\ WF_vars(ChangeS3)
    /\ WF_vars(ChangeS4)
    /\ WF_vars(ChangeSw1)
    /\ WF_vars(ChangeSw2)

Spec == Init /\ [][Next]_vars /\ Fairness
----
TrainsNeverCollide == t1 /= t2
Train1Crossed == t1 = "TRACK4"
Train2Crossed == t2 = "TRACK1"
EventuallyCrossingSuccessful == <>(Train1Crossed /\ Train2Crossed)
====