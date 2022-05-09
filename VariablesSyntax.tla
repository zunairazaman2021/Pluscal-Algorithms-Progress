-------------------------- MODULE VariablesSyntax --------------------------
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
     A: x := x+2 ;
end process
begin 
    B: x := x+1;
end subprocess
begin sub \in [2..3]
    C: x := x+1;
end subprocess


process q \in ProcessesQ
variables y = 0;
begin
     D: y := y + 2 ;
end process
begin 
    E: y := x * y;
end subprocess
begin 
    F: y := y+2;
end subprocess
begin sub \in [4..5]
    variables z=0;
    G: y := y-1;
       z := z + 1;
end subprocess
end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-f88dedee0590bbc06eaaab42684a01df
VARIABLES x, y, z, pc

vars == << x, y,z, pc >>

ProcSet == (Processes) \cup (ProcessesQ)
Procs1 == {<<p>>: p \in Processes}
Procs1SingleThreads1 == {<<p,1>>: p \in Processes}
Procs1ReplicatedThreads2 == {<<p, 2, i>>: p \in Processes, i \in 2..3 }

Procs2 == {<<p>>: p \in ProcessesQ}
Procs2SingleThreads1 == {<<p,1>>: p \in ProcessesQ}
Procs2SingleThreads2 == {<<p,2>>: p \in ProcessesQ}
Procs2ReplicatedThreads3 == {<<p, 3, i>>: p \in ProcessesQ, i \in 4..5 }

Init == (* Global variables *)
        /\ x = [self \in Processes |-> 0]
        /\ y = [self \in ProcessesQ |-> 0]
        /\ z = [self \in 4..5 |-> 0]  \*might not be a good syntax here
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
           /\ x' = [x EXCEPT ![self] = x[self] + 2]
           /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]
           /\ y' = y
           /\ z' = z

B(self) == /\ pc[<<self, 1>>]  = "B"
           /\ x' = [x EXCEPT ![self] = x[self] + 1]
           /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]
           /\ y' = y
           /\ z' = z
C(self, i) == /\ pc[<<self, 2, i>>]  = "C"
           /\ x' = [x EXCEPT ![self] = x[self] + 1]
           /\ pc' = [pc EXCEPT ![<<self, 2, i>>] = "Done"]
           /\ y' = y
           /\ z' = z

p(self) == A(self)
pthread1(self) == B(self)
pthread2(self,i) == C(self,i)
     

D(self) == /\ pc[<<self>>]  = "D"
           /\ y' = [y EXCEPT ![self] = y[self] + 2]
           /\ pc' = [pc EXCEPT ![<<self>>]= "Done"]
           /\ x' = x
           /\ z' = z

E(self) == /\ pc[<<self, 1>>]  = "E"
           /\ y' = [y EXCEPT ![self] = x[self] * y[self]] 
           /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]
           /\ x' = x
           /\ z' = z
F(self) == /\ pc[<<self, 2>>]  = "F"
           /\ y' = [y EXCEPT ![self] = y[self] + 2]
           /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]
           /\ x' = x
           /\ z' = z
G(self, i) == /\ pc[<<self, 3, i>>]  = "G"
              /\ y' = [y EXCEPT ![self] = y[self] - 1]
              /\ z' = [z EXCEPT ![self] = z[self] + 1]
              /\ pc' = [pc EXCEPT ![<<self, 2, i>>] = "Done"]
              /\ x'= x
           
           
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
\* Last modified Mon May 09 09:54:44 GMT 2022 by zunai
\* Created Mon May 09 07:58:01 GMT 2022 by zunai
