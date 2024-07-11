---- MODULE spec ----
EXTENDS TLC, Integers, FiniteSets

(*--algorithm spec

variables 
    a = 0,
    threads = 1..2,
    entered_critical_section = {};

define
    OnlyOneThreadEntersCriticalSection == Cardinality(entered_critical_section) <= 1
end define;

process Thread \in threads
variables 
    tmp = 0;
begin
Load:
    tmp := a;
Store:
    a := tmp + 1;
CriticalSectionCheck:
    if a = 1 then
        entered_critical_section := entered_critical_section \union {self};
    end if; 
end process;

end algorithm; *)
====