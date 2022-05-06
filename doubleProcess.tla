--------------------------- MODULE doubleProcess ---------------------------

EXTENDS TLC, Naturals, Integers, Sequences
CONSTANT P, Q
ASSUME P \in Nat
Processes == 1..P
ProcessesQ == P+1..Q
(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Syntax
variables x = 0;
process p \in Processes
begin
     A: x := x+1 ;
end process
begin 
    B: x := x+1;
end subprocess
begin sub \in [2..3]
    C: x := x+1;
end subprocess


process q \in ProcessesQ
begin
     D: x := x+1 ;
end process
begin 
    E: x := x+1;
end subprocess
begin 
    F: x := x+1;
end subprocess
begin sub \in [4..5]
    G: x := x+1;
end subprocess
end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-f88dedee0590bbc06eaaab42684a01df
VARIABLES x, pc

vars == << x, pc >>

ProcSet == (Processes) \cup (ProcessesQ)
Procs1 == {<<p>>: p \in Processes}
Procs1SingleThreads1 == {<<p,1>>: p \in Processes}
Procs1ReplicatedThreads2 == {<<p, 2, i>>: p \in Processes, i \in 2..3 }

Procs2 == {<<p>>: p \in ProcessesQ}
Procs2SingleThreads1 == {<<p,1>>: p \in ProcessesQ}
Procs2SingleThreads2 == {<<p,2>>: p \in ProcessesQ}
Procs2ReplicatedThreads3 == {<<p, 3, i>>: p \in ProcessesQ, i \in 4..5 }

 
                (*  CASE p \in Procs1 -> IF p \in Procs1 THEN "A" 
                                       ELSE IF p \in Procs1SingleThreads1 THEN "B"
                                       ELSE IF Procs1ReplicatedThreads2 THEN "C"
                                       ELSE 0
                  [] p \in Procs2 -> IF p \in Procs2 THEN "D" 
                                    ELSE IF p \in Procs2SingleThreads1 THEN "E"
                                    ELSE IF p \in Procs2SingleThreads2 THEN "F"
                                    ELSE  IF Procs2ReplicatedThreads3 THEN "G"
                                    ELSE 0
                 *)
Init == (* Global variables *)
        /\ x = 0
        /\ pc = [ p \in Procs1 \union Procs2 \union Procs1SingleThreads1 
                     \union Procs1ReplicatedThreads2 
                     \union Procs2SingleThreads1 
                     \union Procs2SingleThreads2
                     \union Procs2ReplicatedThreads3
                  |-> CASE p \in Procs1 -> "A"
                  [] p \in Procs1SingleThreads1 -> "B"
                  [] p \in Procs1ReplicatedThreads2 -> "C"
                  [] p \in Procs2 -> "D"
                  [] p \in Procs2SingleThreads1 -> "E"
                  [] p \in Procs2SingleThreads2 -> "F"
                  [] p \in Procs2ReplicatedThreads3 -> "G"
                  ]   
                         
A(self) == /\ pc[<<self>>]  = "A"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]

B(self) == /\ pc[<<self, 1>>]  = "B"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]
C(self, i) == /\ pc[<<self, 2, i>>]  = "C"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self, 2, i>>] = "Done"]

p(self) == A(self)
pthread1(self) == B(self)
pthread2(self,i) == C(self,i)
     

D(self) == /\ pc[<<self>>]  = "D"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self>>]= "Done"]

E(self) == /\ pc[<<self, 1>>]  = "E"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]
           
F(self) == /\ pc[<<self, 2>>]  = "F"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]
G(self, i) == /\ pc[<<self, 3, i>>]  = "G"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self, 2, i>>] = "Done"]
           
           
q(self) == D(self)

qthread1(self) == E(self)
qthread2(self) == F(self)
qthread3(self,i) == G(self,i)


(* Allow infinite stuttering to prevent deadlock on termination. *)

Next ==   \/ \E self \in Processes : p(self)
          \/ \E self \in Processes : pthread1(self)
          \/ \E self \in Processes, i \in 2..3 : pthread2(self, i)      
          \/ \E self \in ProcessesQ : q(self)
          \/ \E self \in ProcessesQ : qthread1(self)
          \/ \E self \in ProcessesQ : qthread2(self)
          \/ \E self \in ProcessesQ, i \in 4..5 : qthread3(self, i)      
          


\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c707b16f6be8aa8dd96482891c8e86cd


=============================================================================
\* Modification History
\* Last modified Fri May 06 15:47:09 GMT 2022 by zunai
\* Created Fri May 06 11:09:27 GMT 2022 by zunai
