---- MODULE spec ----
EXTENDS TLC, Sequences, Integers, FiniteSets

(*--algorithm spec
variables
    capacity = [thrash |-> 10, recycle |-> 10],
    bins = [thrash |-> {}, recycle |-> {}],
    count = [thrash |-> 0, recycle |-> 0],
    items = <<
        [type |-> "recycle", size |-> 5],
        [type |-> "thrash", size |-> 5],
        [type |-> "recycle", size |-> 4],
        [type |-> "recycle", size |-> 3]
    >>,
    curr = "";

macro add_item(type) begin
    bins[type] := bins[type] \union {curr};
    capacity[type] := capacity[type] - curr.size;
    count[type] := count[type] + 1;
end macro;

begin
    \* While items not empty
    while items /= <<>> do
        \* Take the first item
        curr := Head(items);
        \* Remove the first item from items
        items := Tail(items);

        \* /\ means AND
        if curr.type = "recycle" /\ curr.size < capacity.recycle then
            add_item("recycle");
        elsif curr.size < capacity.thrash then
            add_item("thrash");
        end if;
    end while;

    assert capacity.thrash >= 0 /\ capacity.recycle >= 0;
    assert Cardinality(bins.thrash) = count.thrash;
    assert Cardinality(bins.recycle) = count.recycle;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "797b21e" /\ chksum(tla) = "daa18811")
VARIABLES capacity, bins, count, items, curr, pc

vars == << capacity, bins, count, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity = [thrash |-> 10, recycle |-> 10]
        /\ bins = [thrash |-> {}, recycle |-> {}]
        /\ count = [thrash |-> 0, recycle |-> 0]
        /\ items =         <<
                       [type |-> "recycle", size |-> 5],
                       [type |-> "thrash", size |-> 5],
                       [type |-> "recycle", size |-> 4],
                       [type |-> "recycle", size |-> 3]
                   >>
        /\ curr = ""
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= <<>>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF curr'.type = "recycle" /\ curr'.size < capacity.recycle
                          THEN /\ bins' = [bins EXCEPT !["recycle"] = bins["recycle"] \union {curr'}]
                               /\ capacity' = [capacity EXCEPT !["recycle"] = capacity["recycle"] - curr'.size]
                               /\ count' = [count EXCEPT !["recycle"] = count["recycle"] + 1]
                          ELSE /\ IF curr'.size < capacity.thrash
                                     THEN /\ bins' = [bins EXCEPT !["thrash"] = bins["thrash"] \union {curr'}]
                                          /\ capacity' = [capacity EXCEPT !["thrash"] = capacity["thrash"] - curr'.size]
                                          /\ count' = [count EXCEPT !["thrash"] = count["thrash"] + 1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(capacity.thrash >= 0 /\ capacity.recycle >= 0, 
                              "Failure of assertion at line 39, column 5.")
                    /\ Assert(Cardinality(bins.thrash) = count.thrash, 
                              "Failure of assertion at line 40, column 5.")
                    /\ Assert(Cardinality(bins.recycle) = count.recycle, 
                              "Failure of assertion at line 41, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << capacity, bins, count, items, curr >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
