---------------------------- MODULE MaxAlgorithm ----------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS IntSet, MaxSeqLen
ASSUME IntSet \subseteq Int
ASSUME MaxSeqLen > 0
PT == INSTANCE PT
Max(seq) == 
   LET set == {seq[i]: i \in 1..Len(seq)} 
   IN  CHOOSE x \in set: \A y \in set: y <= x
   
AllInputs == PT!SeqOf(IntSet, MaxSeqLen) \ {<<>>}
(*--algorithm max
variables seq \in AllInputs, i=1, max;
begin
     assert Len(seq) > 0;
     max := seq[1];
     while i <= Len(seq) do
         if max < seq[i] then 
            max := seq[i];
         end if;
         i := i+1;
     end while;
     assert max = Max(seq);

end algorithm;*)   
\* BEGIN TRANSLATION (chksum(pcal) = "b70f0b56" /\ chksum(tla) = "3780b99d")
CONSTANT defaultInitValue
VARIABLES seq, i, max, pc

vars == << seq, i, max, pc >>

Init == (* Global variables *)
        /\ seq \in AllInputs
        /\ i = 1
        /\ max = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(Len(seq) > 0, 
                   "Failure of assertion at line 15, column 6.")
         /\ max' = seq[1]
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << seq, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i <= Len(seq)
               THEN /\ IF max < seq[i]
                          THEN /\ max' = seq[i]
                          ELSE /\ TRUE
                               /\ max' = max
                    /\ i' = i+1
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(max = Max(seq), 
                              "Failure of assertion at line 23, column 6.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << i, max >>
         /\ seq' = seq

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Mar 10 00:27:15 GMT+12:00 2022 by zunai
\* Created Wed Mar 09 22:54:26 GMT+12:00 2022 by zunai
