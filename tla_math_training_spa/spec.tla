---- MODULE spec ----
EXTENDS TLC, Naturals

\* https://arxiv.org/pdf/2005.05627

CONSTANTS  MaxNumQuestions

VARIABLES num, input_enabled, check_enabled, new_question_enabled, result, count_right, count_wrong

vars == <<num, input_enabled, check_enabled, new_question_enabled, result, count_right, count_wrong>>

Init ==
    /\ num = 1
    /\ count_right = 0
    /\ count_wrong = 0
    /\ input_enabled = TRUE
    /\ check_enabled = FALSE
    /\ new_question_enabled = FALSE
    /\ result = ""

TypeOk ==
    /\ num \in Nat
    /\ count_right \in Nat
    /\ count_wrong \in Nat
    /\ input_enabled \in BOOLEAN 
    /\ check_enabled \in BOOLEAN 
    /\ new_question_enabled \in BOOLEAN 
    /\ result \in {"", "Right", "Wrong"}

InputAnswer ==
    /\ input_enabled
    /\ input_enabled' = FALSE
    /\ check_enabled' = TRUE
    /\ UNCHANGED <<num, new_question_enabled, result, count_right, count_wrong>>

Check ==
    /\ check_enabled
    /\ check_enabled' = FALSE
    /\ new_question_enabled' = TRUE
    /\ \E answer_correct \in BOOLEAN:
        IF answer_correct THEN 
            /\ count_right' = count_right + 1
            /\ result' = "Right"
            /\ UNCHANGED <<count_wrong>>
        ELSE 
            /\ count_wrong' = count_wrong + 1
            /\ result' = "Wrong"
            /\ UNCHANGED <<count_right>>
    /\ UNCHANGED <<num, input_enabled>>

NewQuestion ==
    /\ num < MaxNumQuestions
    /\ new_question_enabled
    /\ new_question_enabled' = FALSE
    /\ num' = num + 1
    /\ input_enabled' = TRUE
    /\ result' = ""
    /\ UNCHANGED <<check_enabled, count_right, count_wrong>>

Terminating ==
    /\ num = MaxNumQuestions
    /\ UNCHANGED vars

Next ==
    \/ InputAnswer
    \/ Check
    \/ NewQuestion
    \/ Terminating

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

Reachability == \A i \in 1..MaxNumQuestions: <>(num = i)

Liveness == input_enabled ~> new_question_enabled

Invariant == result = "" \/ num = count_right + count_wrong
====