----------------------------- MODULE NewSyntax -----------------------------
EXTENDS TLC, Naturals, Integers, Sequences
CONSTANT P
ASSUME P \in Nat
Processes == 1..P
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

begin sub \in  [2..3]
    C: x := x+1;
end subprocess
end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-f871e5030ee8d7ccf69334df695f23e8
VARIABLES x, pc
vars == << x, pc >>

Procs == {<<p>>: p \in Processes}
SingleThreads == {<<p,1>>: p \in Processes}
ReplicatedThreads == {<<p, 2, i>>: p \in Processes, i \in 2..3 }

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [p \in Procs \union SingleThreads \union ReplicatedThreads |->
                         IF p \in Procs THEN <<"A">>
                         ELSE IF p \in SingleThreads THEN <<"B">>
                         ELSE IF p \in ReplicatedThreads THEN <<"C">>
                         ELSE  "C"]

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
thread1(self) == B(self)
thread2(self,i) == C(self,i)

Next ==   \/ \E self \in Procs : p(self)
          \/ \E self \in Procs : thread1(self)
          \/ \E self \in Procs, i \in 2..3 : thread2(self, i)
\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-7e4a746bad9b083869902a37b1f134c0



=============================================================================
\* Modification History
\* Last modified Thu May 05 08:56:59 GMT 2022 by zunai
\* Created Tue May 03 11:13:21 GMT 2022 by zunai
