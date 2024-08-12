---- MODULE spec ----
EXTENDS TLC

(*--algorithm spec
variables
    open = FALSE,
    locked = FALSE,
    key \in BOOLEAN;

begin
Event:
    either
        await locked /\ (open \/ key);
        locked := FALSE;
    or
        await ~locked;
        locked := TRUE;
    or
        await ~locked /\ (open \/ key);
        await ~open;
        open := TRUE;
    or
        await open;
        open := FALSE;
    end either;
    goto Event;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3dd2a94a" /\ chksum(tla) = "dd85662")
VARIABLES open, locked, key, pc

vars == << open, locked, key, pc >>

Init == (* Global variables *)
        /\ open = FALSE
        /\ locked = FALSE
        /\ key \in BOOLEAN
        /\ pc = "Event"

Event == /\ pc = "Event"
         /\ \/ /\ locked /\ (open \/ key)
               /\ locked' = FALSE
               /\ open' = open
            \/ /\ ~locked
               /\ locked' = TRUE
               /\ open' = open
            \/ /\ ~locked /\ (open \/ key)
               /\ ~open
               /\ open' = TRUE
               /\ UNCHANGED locked
            \/ /\ open
               /\ open' = FALSE
               /\ UNCHANGED locked
         /\ pc' = "Event"
         /\ key' = key

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Event
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
