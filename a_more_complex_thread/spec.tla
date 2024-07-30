---- MODULE spec ----
EXTENDS TLC, Sequences, FiniteSets, Integers

NULL == <<"-1", -1>>

(*--algorithm spec
variables
    mutex = NULL,
    mutex2 = NULL,
    mutex3 = NULL,
    flag = FALSE; 
macro enter(mutex, thread) begin
    await mutex = NULL \/ mutex[1] = thread;
    if mutex = NULL then
        mutex := <<thread, 1>>;
    else 
        mutex := <<thread, mutex[2] + 1>>;
    end if;
end macro;

macro exit(mutex, thread) begin
    assert mutex[1] = thread;
    assert mutex[2] > 0;

    if mutex[2] = 1 then
        mutex := NULL;
    else
        mutex := <<mutex[1], mutex[2] - 1>>;
    end if;
end macro;

macro try_enter(mutex, thread) begin
    if mutex = NULL then
        mutex := <<thread, 1>>;
        try_enter_result := TRUE;
    elsif mutex[1] = thread then 
        mutex := <<thread, mutex[2] + 1>>;
        try_enter_result := TRUE;
    else 
        try_enter_result := FALSE;
    end if;
end macro;

process thread_a = "a"
variables
    try_enter_result = FALSE;
begin
Loop:
while TRUE do
TryEnterMutex: try_enter(mutex, "a");
CheckEnterMutex:
    if try_enter_result then
        EnterMutex3: enter(mutex3, "a");
        EnterMutex: enter(mutex, "a");
        ExitMutex: exit(mutex, "a");
        EnterMutex2: enter(mutex2, "a");
    else 
        Else_EnterMutex2: enter(mutex2, "a");
        SetFlag: flag := TRUE;
        ExitMutex2: exit(mutex2, "a");
    end if;
end while;
end process;

process thread_b = "b"
begin
Loop:
while TRUE do
    CheckFlag:
    if flag then
        EnterMutex2:enter(mutex2, "b");
        EnterMutex: enter(mutex, "b");
        SetFlag:flag := FALSE;
        ExitMutex: exit(mutex, "b");
        ExitMutex2: enter(mutex2, "b");
    else 
        Else_EnterMutex: enter(mutex, "b"); 
        Else_SetFlag: flag := FALSE;
        Else_ExitMutex: exit(mutex, "b");
    end if;
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "eb6f53df" /\ chksum(tla) = "c1c0244a")
\* Label Loop of process thread_a at line 49 col 1 changed to Loop_
\* Label EnterMutex of process thread_a at line 13 col 5 changed to EnterMutex_
\* Label ExitMutex of process thread_a at line 22 col 5 changed to ExitMutex_
\* Label EnterMutex2 of process thread_a at line 13 col 5 changed to EnterMutex2_
\* Label SetFlag of process thread_a at line 59 col 18 changed to SetFlag_
\* Label ExitMutex2 of process thread_a at line 22 col 5 changed to ExitMutex2_
VARIABLES mutex, mutex2, mutex3, flag, pc, try_enter_result

vars == << mutex, mutex2, mutex3, flag, pc, try_enter_result >>

ProcSet == {"a"} \cup {"b"}

Init == (* Global variables *)
        /\ mutex = NULL
        /\ mutex2 = NULL
        /\ mutex3 = NULL
        /\ flag = FALSE
        (* Process thread_a *)
        /\ try_enter_result = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "a" -> "Loop_"
                                        [] self = "b" -> "Loop"]

Loop_ == /\ pc["a"] = "Loop_"
         /\ pc' = [pc EXCEPT !["a"] = "TryEnterMutex"]
         /\ UNCHANGED << mutex, mutex2, mutex3, flag, try_enter_result >>

TryEnterMutex == /\ pc["a"] = "TryEnterMutex"
                 /\ IF mutex = NULL
                       THEN /\ mutex' = <<"a", 1>>
                            /\ try_enter_result' = TRUE
                       ELSE /\ IF mutex[1] = "a"
                                  THEN /\ mutex' = <<"a", mutex[2] + 1>>
                                       /\ try_enter_result' = TRUE
                                  ELSE /\ try_enter_result' = FALSE
                                       /\ mutex' = mutex
                 /\ pc' = [pc EXCEPT !["a"] = "CheckEnterMutex"]
                 /\ UNCHANGED << mutex2, mutex3, flag >>

CheckEnterMutex == /\ pc["a"] = "CheckEnterMutex"
                   /\ IF try_enter_result
                         THEN /\ pc' = [pc EXCEPT !["a"] = "EnterMutex3"]
                         ELSE /\ pc' = [pc EXCEPT !["a"] = "Else_EnterMutex2"]
                   /\ UNCHANGED << mutex, mutex2, mutex3, flag, 
                                   try_enter_result >>

EnterMutex3 == /\ pc["a"] = "EnterMutex3"
               /\ mutex3 = NULL \/ mutex3[1] = "a"
               /\ IF mutex3 = NULL
                     THEN /\ mutex3' = <<"a", 1>>
                     ELSE /\ mutex3' = <<"a", mutex3[2] + 1>>
               /\ pc' = [pc EXCEPT !["a"] = "EnterMutex_"]
               /\ UNCHANGED << mutex, mutex2, flag, try_enter_result >>

EnterMutex_ == /\ pc["a"] = "EnterMutex_"
               /\ mutex = NULL \/ mutex[1] = "a"
               /\ IF mutex = NULL
                     THEN /\ mutex' = <<"a", 1>>
                     ELSE /\ mutex' = <<"a", mutex[2] + 1>>
               /\ pc' = [pc EXCEPT !["a"] = "ExitMutex_"]
               /\ UNCHANGED << mutex2, mutex3, flag, try_enter_result >>

ExitMutex_ == /\ pc["a"] = "ExitMutex_"
              /\ Assert(mutex[1] = "a", 
                        "Failure of assertion at line 22, column 5 of macro called at line 55, column 20.")
              /\ Assert(mutex[2] > 0, 
                        "Failure of assertion at line 23, column 5 of macro called at line 55, column 20.")
              /\ IF mutex[2] = 1
                    THEN /\ mutex' = NULL
                    ELSE /\ mutex' = <<mutex[1], mutex[2] - 1>>
              /\ pc' = [pc EXCEPT !["a"] = "EnterMutex2_"]
              /\ UNCHANGED << mutex2, mutex3, flag, try_enter_result >>

EnterMutex2_ == /\ pc["a"] = "EnterMutex2_"
                /\ mutex2 = NULL \/ mutex2[1] = "a"
                /\ IF mutex2 = NULL
                      THEN /\ mutex2' = <<"a", 1>>
                      ELSE /\ mutex2' = <<"a", mutex2[2] + 1>>
                /\ pc' = [pc EXCEPT !["a"] = "Loop_"]
                /\ UNCHANGED << mutex, mutex3, flag, try_enter_result >>

Else_EnterMutex2 == /\ pc["a"] = "Else_EnterMutex2"
                    /\ mutex2 = NULL \/ mutex2[1] = "a"
                    /\ IF mutex2 = NULL
                          THEN /\ mutex2' = <<"a", 1>>
                          ELSE /\ mutex2' = <<"a", mutex2[2] + 1>>
                    /\ pc' = [pc EXCEPT !["a"] = "SetFlag_"]
                    /\ UNCHANGED << mutex, mutex3, flag, try_enter_result >>

SetFlag_ == /\ pc["a"] = "SetFlag_"
            /\ flag' = TRUE
            /\ pc' = [pc EXCEPT !["a"] = "ExitMutex2_"]
            /\ UNCHANGED << mutex, mutex2, mutex3, try_enter_result >>

ExitMutex2_ == /\ pc["a"] = "ExitMutex2_"
               /\ Assert(mutex2[1] = "a", 
                         "Failure of assertion at line 22, column 5 of macro called at line 60, column 21.")
               /\ Assert(mutex2[2] > 0, 
                         "Failure of assertion at line 23, column 5 of macro called at line 60, column 21.")
               /\ IF mutex2[2] = 1
                     THEN /\ mutex2' = NULL
                     ELSE /\ mutex2' = <<mutex2[1], mutex2[2] - 1>>
               /\ pc' = [pc EXCEPT !["a"] = "Loop_"]
               /\ UNCHANGED << mutex, mutex3, flag, try_enter_result >>

thread_a == Loop_ \/ TryEnterMutex \/ CheckEnterMutex \/ EnterMutex3
               \/ EnterMutex_ \/ ExitMutex_ \/ EnterMutex2_
               \/ Else_EnterMutex2 \/ SetFlag_ \/ ExitMutex2_

Loop == /\ pc["b"] = "Loop"
        /\ pc' = [pc EXCEPT !["b"] = "CheckFlag"]
        /\ UNCHANGED << mutex, mutex2, mutex3, flag, try_enter_result >>

CheckFlag == /\ pc["b"] = "CheckFlag"
             /\ IF flag
                   THEN /\ pc' = [pc EXCEPT !["b"] = "EnterMutex2"]
                   ELSE /\ pc' = [pc EXCEPT !["b"] = "Else_EnterMutex"]
             /\ UNCHANGED << mutex, mutex2, mutex3, flag, try_enter_result >>

EnterMutex2 == /\ pc["b"] = "EnterMutex2"
               /\ mutex2 = NULL \/ mutex2[1] = "b"
               /\ IF mutex2 = NULL
                     THEN /\ mutex2' = <<"b", 1>>
                     ELSE /\ mutex2' = <<"b", mutex2[2] + 1>>
               /\ pc' = [pc EXCEPT !["b"] = "EnterMutex"]
               /\ UNCHANGED << mutex, mutex3, flag, try_enter_result >>

EnterMutex == /\ pc["b"] = "EnterMutex"
              /\ mutex = NULL \/ mutex[1] = "b"
              /\ IF mutex = NULL
                    THEN /\ mutex' = <<"b", 1>>
                    ELSE /\ mutex' = <<"b", mutex[2] + 1>>
              /\ pc' = [pc EXCEPT !["b"] = "SetFlag"]
              /\ UNCHANGED << mutex2, mutex3, flag, try_enter_result >>

SetFlag == /\ pc["b"] = "SetFlag"
           /\ flag' = FALSE
           /\ pc' = [pc EXCEPT !["b"] = "ExitMutex"]
           /\ UNCHANGED << mutex, mutex2, mutex3, try_enter_result >>

ExitMutex == /\ pc["b"] = "ExitMutex"
             /\ Assert(mutex[1] = "b", 
                       "Failure of assertion at line 22, column 5 of macro called at line 74, column 20.")
             /\ Assert(mutex[2] > 0, 
                       "Failure of assertion at line 23, column 5 of macro called at line 74, column 20.")
             /\ IF mutex[2] = 1
                   THEN /\ mutex' = NULL
                   ELSE /\ mutex' = <<mutex[1], mutex[2] - 1>>
             /\ pc' = [pc EXCEPT !["b"] = "ExitMutex2"]
             /\ UNCHANGED << mutex2, mutex3, flag, try_enter_result >>

ExitMutex2 == /\ pc["b"] = "ExitMutex2"
              /\ mutex2 = NULL \/ mutex2[1] = "b"
              /\ IF mutex2 = NULL
                    THEN /\ mutex2' = <<"b", 1>>
                    ELSE /\ mutex2' = <<"b", mutex2[2] + 1>>
              /\ pc' = [pc EXCEPT !["b"] = "Loop"]
              /\ UNCHANGED << mutex, mutex3, flag, try_enter_result >>

Else_EnterMutex == /\ pc["b"] = "Else_EnterMutex"
                   /\ mutex = NULL \/ mutex[1] = "b"
                   /\ IF mutex = NULL
                         THEN /\ mutex' = <<"b", 1>>
                         ELSE /\ mutex' = <<"b", mutex[2] + 1>>
                   /\ pc' = [pc EXCEPT !["b"] = "Else_SetFlag"]
                   /\ UNCHANGED << mutex2, mutex3, flag, try_enter_result >>

Else_SetFlag == /\ pc["b"] = "Else_SetFlag"
                /\ flag' = FALSE
                /\ pc' = [pc EXCEPT !["b"] = "Else_ExitMutex"]
                /\ UNCHANGED << mutex, mutex2, mutex3, try_enter_result >>

Else_ExitMutex == /\ pc["b"] = "Else_ExitMutex"
                  /\ Assert(mutex[1] = "b", 
                            "Failure of assertion at line 22, column 5 of macro called at line 79, column 25.")
                  /\ Assert(mutex[2] > 0, 
                            "Failure of assertion at line 23, column 5 of macro called at line 79, column 25.")
                  /\ IF mutex[2] = 1
                        THEN /\ mutex' = NULL
                        ELSE /\ mutex' = <<mutex[1], mutex[2] - 1>>
                  /\ pc' = [pc EXCEPT !["b"] = "Loop"]
                  /\ UNCHANGED << mutex2, mutex3, flag, try_enter_result >>

thread_b == Loop \/ CheckFlag \/ EnterMutex2 \/ EnterMutex \/ SetFlag
               \/ ExitMutex \/ ExitMutex2 \/ Else_EnterMutex
               \/ Else_SetFlag \/ Else_ExitMutex

Next == thread_a \/ thread_b

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
