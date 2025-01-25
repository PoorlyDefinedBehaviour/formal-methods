---- MODULE Sequential ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

VARIABLES pc

ToSequentialID(i, id) ==
    IF id \in STRING THEN 
        ToString(i) \o "_" \o id
    ELSE 
        ToString(i) \o "_" \o ToString(id) 

Sequential2(id, f1_id, f1(_), f2_id, f2(_)) == 
    LET 
        seq_f1_id == ToSequentialID(1, f1_id)
        seq_f2_id == ToSequentialID(2, f2_id)
    IN
    /\ Assert(Cardinality({seq_f1_id, seq_f2_id}) = 2, "Duplicate ids found")
    /\ 
        \/ id \notin DOMAIN pc /\ f1(1) /\ pc' = pc @@ [v \in {id} |-> seq_f2_id]
        \/ /\ id \in DOMAIN pc 
           /\ \/ pc[id] = seq_f1_id /\ f1(1) /\ pc' = [pc EXCEPT ![id] = seq_f2_id]
              \/ pc[id] = seq_f2_id /\ f2(2) /\ pc' = [pc EXCEPT ![id] = "Done"]

Sequential3(id, f1_id, f1(_), f2_id, f2(_), f3_id, f3(_)) == 
    LET 
        seq_f1_id == ToSequentialID(1, f1_id)
        seq_f2_id == ToSequentialID(2, f2_id)
        seq_f3_id == ToSequentialID(3, f3_id)
    IN
    /\ Assert(Cardinality({seq_f1_id, seq_f2_id, seq_f3_id}) = 3, "Duplicate ids found")
    /\ 
        \/ id \notin DOMAIN pc /\ f1(1) /\ pc' = pc @@ [v \in {id} |-> seq_f2_id]
        \/ /\ id \in DOMAIN pc 
           /\ \/ pc[id] = seq_f1_id /\ f1(1) /\ pc' = [pc EXCEPT ![id] = seq_f2_id]
              \/ pc[id] = seq_f2_id /\ f2(2) /\ pc' = [pc EXCEPT ![id] = seq_f3_id]
              \/ pc[id] = seq_f3_id /\ f3(3) /\ pc' = [pc EXCEPT ![id] = "Done"]

Sequential4(id, f1_id, f1(_), f2_id, f2(_), f3_id, f3(_), f4_id, f4(_)) == 
    LET 
        seq_f1_id == ToSequentialID(1, f1_id)
        seq_f2_id == ToSequentialID(2, f2_id)
        seq_f3_id == ToSequentialID(3, f3_id)
        seq_f4_id == ToSequentialID(4, f4_id)
    IN
    /\ Assert(Cardinality({seq_f1_id, seq_f2_id, seq_f3_id, seq_f4_id}) = 4, "Duplicate ids found")
    /\ 
        \/ id \notin DOMAIN pc /\ f1(1) /\ pc' = pc @@ [v \in {id} |-> seq_f2_id]
        \/ /\ id \in DOMAIN pc 
           /\ \/ pc[id] = seq_f1_id /\ f1(1) /\ pc' = [pc EXCEPT ![id] = seq_f2_id]
              \/ pc[id] = seq_f2_id /\ f2(2) /\ pc' = [pc EXCEPT ![id] = seq_f3_id]
              \/ pc[id] = seq_f3_id /\ f3(3) /\ pc' = [pc EXCEPT ![id] = seq_f4_id]
              \/ pc[id] = seq_f4_id /\ f4(4) /\ pc' = [pc EXCEPT ![id] = "Done"]

Sequential5(id, f1_id, f1(_), f2_id, f2(_), f3_id, f3(_), f4_id, f4(_), f5_id, f5(_)) == 
    LET 
        seq_f1_id == ToSequentialID(1, f1_id)
        seq_f2_id == ToSequentialID(2, f2_id)
        seq_f3_id == ToSequentialID(3, f3_id)
        seq_f4_id == ToSequentialID(4, f4_id)
        seq_f5_id == ToSequentialID(5, f5_id)
    IN
    /\ Assert(Cardinality({seq_f1_id, seq_f2_id, seq_f3_id, seq_f4_id, seq_f5_id}) = 5, "Duplicate ids found")
    /\ 
        \/ id \notin DOMAIN pc /\ f1(1) /\ pc' = pc @@ [v \in {id} |-> seq_f2_id]
        \/ /\ id \in DOMAIN pc 
           /\ \/ pc[id] = seq_f1_id /\ f1(1) /\ pc' = [pc EXCEPT ![id] = seq_f2_id]
              \/ pc[id] = seq_f2_id /\ f2(2) /\ pc' = [pc EXCEPT ![id] = seq_f3_id]
              \/ pc[id] = seq_f3_id /\ f3(3) /\ pc' = [pc EXCEPT ![id] = seq_f4_id]
              \/ pc[id] = seq_f4_id /\ f4(4) /\ pc' = [pc EXCEPT ![id] = seq_f5_id]
              \/ pc[id] = seq_f5_id /\ f5(5) /\ pc' = [pc EXCEPT ![id] = "Done"]

Sequential6(id, f1_id, f1(_), f2_id, f2(_), f3_id, f3(_), f4_id, f4(_), f5_id, f5(_), f6_id, f6(_)) == 
    LET 
        seq_f1_id == ToSequentialID(1, f1_id)
        seq_f2_id == ToSequentialID(2, f2_id)
        seq_f3_id == ToSequentialID(3, f3_id)
        seq_f4_id == ToSequentialID(4, f4_id)
        seq_f5_id == ToSequentialID(5, f5_id)
        seq_f6_id == ToSequentialID(6, f6_id)
    IN
    /\ Assert(Cardinality({seq_f1_id, seq_f2_id, seq_f3_id, seq_f4_id, seq_f5_id, seq_f6_id}) = 6, "Duplicate ids found")
    /\ 
        \/ id \notin DOMAIN pc /\ f1(1) /\ pc' = pc @@ [v \in {id} |-> seq_f2_id]
        \/ /\ id \in DOMAIN pc 
           /\ \/ pc[id] = seq_f1_id /\ f1(1) /\ pc' = [pc EXCEPT ![id] = seq_f2_id]
              \/ pc[id] = seq_f2_id /\ f2(2) /\ pc' = [pc EXCEPT ![id] = seq_f3_id]
              \/ pc[id] = seq_f3_id /\ f3(3) /\ pc' = [pc EXCEPT ![id] = seq_f4_id]
              \/ pc[id] = seq_f4_id /\ f4(4) /\ pc' = [pc EXCEPT ![id] = seq_f5_id]
              \/ pc[id] = seq_f5_id /\ f5(5) /\ pc' = [pc EXCEPT ![id] = seq_f6_id]
              \/ pc[id] = seq_f6_id /\ f6(6) /\ pc' = [pc EXCEPT ![id] = "Done"]

Sequential7(id, f1_id, f1(_), f2_id, f2(_), f3_id, f3(_), f4_id, f4(_), f5_id, f5(_), f6_id, f6(_), f7_id, f7(_)) == 
    LET 
        seq_f1_id == ToSequentialID(1, f1_id)
        seq_f2_id == ToSequentialID(2, f2_id)
        seq_f3_id == ToSequentialID(3, f3_id)
        seq_f4_id == ToSequentialID(4, f4_id)
        seq_f5_id == ToSequentialID(5, f5_id)
        seq_f6_id == ToSequentialID(6, f6_id)
        seq_f7_id == ToSequentialID(7, f7_id)
    IN
    /\ Assert(Cardinality({seq_f1_id, seq_f2_id, seq_f3_id, seq_f4_id, seq_f5_id, seq_f6_id, seq_f7_id}) = 7, "Duplicate ids found")
    /\ 
        \/ id \notin DOMAIN pc /\ f1(1) /\ pc' = pc @@ [v \in {id} |-> seq_f2_id]
        \/ /\ id \in DOMAIN pc 
           /\ \/ pc[id] = seq_f1_id /\ f1(1) /\ pc' = [pc EXCEPT ![id] = seq_f2_id]
              \/ pc[id] = seq_f2_id /\ f2(2) /\ pc' = [pc EXCEPT ![id] = seq_f3_id]
              \/ pc[id] = seq_f3_id /\ f3(3) /\ pc' = [pc EXCEPT ![id] = seq_f4_id]
              \/ pc[id] = seq_f4_id /\ f4(4) /\ pc' = [pc EXCEPT ![id] = seq_f5_id]
              \/ pc[id] = seq_f5_id /\ f5(5) /\ pc' = [pc EXCEPT ![id] = seq_f6_id]
              \/ pc[id] = seq_f6_id /\ f6(6) /\ pc' = [pc EXCEPT ![id] = seq_f7_id]
              \/ pc[id] = seq_f7_id /\ f7(7) /\ pc' = [pc EXCEPT ![id] = "Done"]
====