---- MODULE spec ----
EXTENDS TLC, Integers

NULL == -1

(*--algorithm spec
variables 
    data_ptr = NULL;

process thread \in {1, 2}
variables p;
begin
    \* Load acquire.
    LoadDataPtr: p := data_ptr;
    if p = NULL then
        \* Set the pointer to the data.
        StoreP: p := self;
        CompareExchange:
            if data_ptr = NULL then
                \* Store release.
                data_ptr := p;
            else
                \* Load acquire.
                p := data_ptr;
            end if;
    end if;
    Println:
        print(p);
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5ad0ded3" /\ chksum(tla) = "ec3bd2d4")
CONSTANT defaultInitValue
VARIABLES data_ptr, pc, p

vars == << data_ptr, pc, p >>

ProcSet == ({1, 2})

Init == (* Global variables *)
        /\ data_ptr = NULL
        (* Process thread *)
        /\ p = [self \in {1, 2} |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "LoadDataPtr"]

LoadDataPtr(self) == /\ pc[self] = "LoadDataPtr"
                     /\ p' = [p EXCEPT ![self] = data_ptr]
                     /\ IF p'[self] = NULL
                           THEN /\ pc' = [pc EXCEPT ![self] = "StoreP"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Println"]
                     /\ UNCHANGED data_ptr

StoreP(self) == /\ pc[self] = "StoreP"
                /\ p' = [p EXCEPT ![self] = self]
                /\ pc' = [pc EXCEPT ![self] = "CompareExchange"]
                /\ UNCHANGED data_ptr

CompareExchange(self) == /\ pc[self] = "CompareExchange"
                         /\ IF data_ptr = NULL
                               THEN /\ data_ptr' = p[self]
                                    /\ p' = p
                               ELSE /\ p' = [p EXCEPT ![self] = data_ptr]
                                    /\ UNCHANGED data_ptr
                         /\ pc' = [pc EXCEPT ![self] = "Println"]

Println(self) == /\ pc[self] = "Println"
                 /\ PrintT((p[self]))
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << data_ptr, p >>

thread(self) == LoadDataPtr(self) \/ StoreP(self) \/ CompareExchange(self)
                   \/ Println(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {1, 2}: thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
