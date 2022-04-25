----------------------------- MODULE TwoThreads -----------------------------
EXTENDS Naturals, TLC
(* PlusCal options (-distpcal) *)
(*
--algorithm threads {
  variables x=0, y=0;
  
  process (thread1 = "thr1")
  { start1:  skip; \* Do nothing at beginning
    1a: if ( y=0 ) {
    1b:     x:=1; } ;
    end1a: if (pc["thr2"] = "Done") { \* If other guy is done
          print <<"x, y:", x, y>> ;
    end1b:   assert ~(x=1 /\ y=1) ; \* Condition "not(x==1 && y==1)" can fail
        }
  } \* end process block
  
  process (thread2 = "thr2")
  { start2:  skip; \* Do nothing at beginning
    2a: if ( x=0 ) {
    2b:     y:=1; } ;
    end2a: if (pc["thr1"] = "Done") { \* If other guy is done
          print <<"x, y:", x, y>> ;
    end2b:   assert ~(x=1 /\ y=1) ; \* Condition "not(x==1 && y==1)" can fail
        }
  } \* end process block

  } \* end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-85bf8a441e798fd8ed01dda7ac0de0c0
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == {"thr1"} \cup {"thr2"}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 = "thr1" THEN 1..1
                               ELSE (**"thr2"**) 1..1]

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ pc = [self \in ProcSet |-> CASE self = "thr1" -> <<"start1">>
                                        [] self = "thr2" -> <<"start2">>]

start1 == /\ pc["thr1"][1]  = "start1"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["thr1"][1] = "1a"]
          /\ UNCHANGED << x, y >>

1a == /\ pc["thr1"][1]  = "1a"
      /\ IF y=0
            THEN /\ pc' = [pc EXCEPT !["thr1"][1] = "1b"]
            ELSE /\ pc' = [pc EXCEPT !["thr1"][1] = "end1a"]
      /\ UNCHANGED << x, y >>

1b == /\ pc["thr1"][1]  = "1b"
      /\ x' = 1
      /\ pc' = [pc EXCEPT !["thr1"][1] = "end1a"]
      /\ y' = y

end1a == /\ pc["thr1"][1]  = "end1a"
         /\ IF pc["thr2"] = "Done"
               THEN /\ PrintT(<<"x, y:", x, y>>)
                    /\ pc' = [pc EXCEPT !["thr1"][1] = "end1b"]
               ELSE /\ pc' = [pc EXCEPT !["thr1"][1] = "Done"]
         /\ UNCHANGED << x, y >>

end1b == /\ pc["thr1"][1]  = "end1b"
         /\ Assert(~(x=1 /\ y=1), 
                   "Failure of assertion at line 14, column 14.")
         /\ pc' = [pc EXCEPT !["thr1"][1] = "Done"]
         /\ UNCHANGED << x, y >>

thread1 == start1 \/ 1a \/ 1b \/ end1a \/ end1b

start2 == /\ pc["thr2"][1]  = "start2"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["thr2"][1] = "2a"]
          /\ UNCHANGED << x, y >>

2a == /\ pc["thr2"][1]  = "2a"
      /\ IF x=0
            THEN /\ pc' = [pc EXCEPT !["thr2"][1] = "2b"]
            ELSE /\ pc' = [pc EXCEPT !["thr2"][1] = "end2a"]
      /\ UNCHANGED << x, y >>

2b == /\ pc["thr2"][1]  = "2b"
      /\ y' = 1
      /\ pc' = [pc EXCEPT !["thr2"][1] = "end2a"]
      /\ x' = x

end2a == /\ pc["thr2"][1]  = "end2a"
         /\ IF pc["thr1"] = "Done"
               THEN /\ PrintT(<<"x, y:", x, y>>)
                    /\ pc' = [pc EXCEPT !["thr2"][1] = "end2b"]
               ELSE /\ pc' = [pc EXCEPT !["thr2"][1] = "Done"]
         /\ UNCHANGED << x, y >>

end2b == /\ pc["thr2"][1]  = "end2b"
         /\ Assert(~(x=1 /\ y=1), 
                   "Failure of assertion at line 24, column 14.")
         /\ pc' = [pc EXCEPT !["thr2"][1] = "Done"]
         /\ UNCHANGED << x, y >>

thread2 == start2 \/ 2a \/ 2b \/ end2a \/ end2b

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == thread1 \/ thread2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-66ad3020041ab119795bf5dd80a544eb


=============================================================================
\* Modification History
\* Last modified Mon Apr 25 08:13:02 GMT 2022 by zunai
\* Created Mon Apr 25 08:12:47 GMT 2022 by zunai
