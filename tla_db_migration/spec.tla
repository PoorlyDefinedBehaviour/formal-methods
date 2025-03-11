---- MODULE spec ----
EXTENDS TLC, Integers, FiniteSets

\* https://biradarganesh25.github.io/pluscal/db_migration.html

CONSTANTS NULL, Tombstone

VARIABLES threads, db, old_db, new_db, bg_migration

vars == <<threads, db, old_db, new_db, bg_migration>>

Threads == {1, 2}
N == 1..4
Objects == [p \in N |-> p]

Init ==
    /\ threads = [t \in Threads |-> [state |-> "PickObject", primary_key |-> NULL, i |-> 0]]
    /\ db = [primary_key \in 1..2 |-> primary_key + 1]
    /\ old_db = [primary_key \in 1..2 |-> primary_key + 1]
    /\ new_db = [primary_key \in {} |-> NULL]
    /\ bg_migration = [state |-> "Start", existing_primary_keys |-> DOMAIN old_db, primary_key |-> NULL]

TypeOk ==
    \/ DOMAIN db \subseteq DOMAIN Objects
    \/ DOMAIN db = {}

----

GetObjectWOMigration(primary_key) ==
    IF primary_key \in DOMAIN db
    THEN db[primary_key]
    ELSE NULL

GetObjectWMigration(primary_key) ==
    IF primary_key \in DOMAIN new_db
    THEN 
        IF new_db[primary_key] = Tombstone
        THEN NULL
        ELSE new_db[primary_key]
    ELSE IF primary_key \in DOMAIN old_db
    THEN old_db[primary_key]        
    ELSE NULL

UpsertWOMigartion(key, value) ==
    db' = (key :> value) @@ db

DeleteWOMigration(key) ==
    IF key \in DOMAIN db THEN
        db' = [p \in DOMAIN db \ {key} |-> db[p]]
    ELSE 
        UNCHANGED db

UpsertWMigration(key, value) ==
    new_db' = (key :> value) @@ new_db

DeleteWMigration(key) ==
    new_db' = (key :> Tombstone) @@ new_db

----

Thread_PickObject ==
    \E t \in Threads:
        /\ threads[t].state = "PickObject"
        /\ \E primary_key \in N:
                threads' = [threads EXCEPT ![t].primary_key = primary_key,
                                           ![t].state = "ChooseOperation"]
        /\ UNCHANGED <<db, old_db, new_db, bg_migration>>
                
Thread_ChooseOperation ==
    \E t \in Threads:
        /\ /\ threads[t].state = "ChooseOperation"
           /\ \/ threads' = [threads EXCEPT ![t].state = "Upsert"]
              \/ threads' = [threads EXCEPT ![t].state = "Delete"]
        /\ UNCHANGED <<db, old_db, new_db, bg_migration>>                                                    

Thread_Upsert ==
    \E t \in Threads:
        /\ threads[t].state = "Upsert"    
        /\ \/ /\ UpsertWOMigartion(threads[t].primary_key, Objects[threads[t].primary_key])
              /\ UpsertWMigration(threads[t].primary_key, Objects[threads[t].primary_key])
           \* Do nothing
           \/ UNCHANGED <<db, new_db>>
        /\ threads' = [threads EXCEPT ![t].state = "IncCounter"]
        /\ UNCHANGED <<old_db, bg_migration>>                                                    

Thread_Delete ==
    \E t \in Threads:
        /\ threads[t].state = "Delete" 
        /\ \/ /\ DeleteWOMigration(threads[t].primary_key)
              /\ DeleteWMigration(threads[t].primary_key)
           \* Do nothing
           \/ UNCHANGED <<db, new_db>>
        /\ threads' = [threads EXCEPT ![t].state = "IncCounter"]
        /\ UNCHANGED <<old_db, bg_migration>>                                                    

Thread_IncCounter ==
    \E t \in Threads:
        /\ threads[t].state = "IncCounter" 
        /\ LET new_i == threads[t].i  + 1 IN 
            /\ threads' = [threads EXCEPT ![t].state = IF new_i < 2 THEN "PickObject" ELSE "Done",
                                          ![t].i = new_i]
        /\ UNCHANGED <<db, old_db, new_db, bg_migration>>                                                       

Thread ==
    \/ Thread_PickObject
    \/ Thread_ChooseOperation
    \/ Thread_Upsert
    \/ Thread_Delete
    \/ Thread_IncCounter

----

BgMigration_Start ==
    /\ bg_migration.state = "Start"
    /\ IF bg_migration.existing_primary_keys = {} 
       THEN bg_migration' = [bg_migration EXCEPT !.state = "Done"]
       ELSE 
        \E primary_key \in bg_migration.existing_primary_keys:
            bg_migration' = [bg_migration EXCEPT !.primary_key = primary_key,
                                                 !.existing_primary_keys = @ \ {primary_key},
                                                 !.state = "Migrate"]
    /\ UNCHANGED <<threads, db, old_db, new_db>>                                                    

BgMigration_Migrate ==
    /\ bg_migration.state = "Migrate"
    /\ IF bg_migration.primary_key \notin DOMAIN new_db
       THEN new_db' = (bg_migration.primary_key :> old_db[bg_migration.primary_key]) @@ new_db
       ELSE UNCHANGED new_db
    /\ bg_migration' = [bg_migration EXCEPT !.state = "Start"]
    /\ UNCHANGED <<threads, db, old_db>>

BgMigration == 
    \/ BgMigration_Start
    \/ BgMigration_Migrate

----

Terminating ==
    /\ \A t \in Threads:
        threads[t].state = "Done"
    /\ bg_migration.state = "Done"
    /\ UNCHANGED vars

Next == 
    \/ Thread
    \/ BgMigration
    \/ Terminating

Spec == Init /\ [][Next]_vars

----

ConsistentViews ==
    \A primary_key \in N:
        GetObjectWOMigration(primary_key) = GetObjectWMigration(primary_key)
====