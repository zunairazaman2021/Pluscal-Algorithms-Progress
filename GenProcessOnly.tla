--------------------------- MODULE GenProcessOnly ---------------------------
EXTENDS TLC, Naturals, Integers, Sequences
CONSTANT P, Q
ASSUME P \in Nat
Processes == 1..P
ProcessesQ == P+1..Q
SubNodes == 4..5

(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Syntax
variables x = 0;
process p \in Processes
begin
     A: x := x+1 ;
     ExA: x := 1 ;
end process
begin
 replicate i \in SubNodes;
     B: x := x+1 ;
     EXBB: x := 0;
end subprocess
begin
 replicate i \in 4..5;
     BX: x := x+1 ;
end subprocess

process q \in ProcessesQ
begin
     D: x := x+1 ;
     ExD: x := x+1;
end process

begin 
    E: x := x+1;
    EXTRA: x := x+1;
end subprocess
begin 
 replicate q \in SubNodes;
    F: x := x+1;
end subprocess
begin 
    replicate i \in SubNodes;
    G: x := x+1;
end subprocess
end algorithm;
*)

\* BEGIN TRANSLATION (chksum(pcal) = "f78b9e5b" /\ chksum(tla) = "9efe3ad8")
VARIABLES x, pc

vars == << x, pc >>

ProcSet == (Processes) \cup (ProcessesQ)

Genprocs1 == { <<p>>: p \in Processes }

Genprocs1Thread1 == { <<p,1,i>>: p \in Processes, i \in SubNodes}

Genprocs1Thread2 == { <<p,2,i>>: p \in Processes, i \in 4..5}

Genprocs2 == { <<p>>: p \in ProcessesQ }

Genprocs2Thread1 == { <<p,1>>: p \in ProcessesQ }

Genprocs2Thread2 == { <<p,2,q>>: p \in ProcessesQ, q \in SubNodes}

Genprocs2Thread3 == { <<p,3,i>>: p \in ProcessesQ, i \in SubNodes}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in Processes THEN 1..3
                                 ELSE (**ProcessesQ**) 1..4]

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in Genprocs1 \union Genprocs1Thread1 \union Genprocs1Thread2 \union Genprocs2 \union Genprocs2Thread1 \union Genprocs2Thread2 \union Genprocs2Thread3 |-> CASE  self \in Genprocs1 -> "A"
		 [] self \in Genprocs1Thread1 -> "B"
		 [] self \in Genprocs1Thread2 -> "BX"
		 [] self \in Genprocs2 -> "D"
		 [] self \in Genprocs2Thread1 -> "E"
		 [] self \in Genprocs2Thread2 -> "F"
		 [] self \in Genprocs2Thread3 -> "G" ]

A(self) == /\ pc[<<self >>] = "A"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self>>] = "ExA"]

ExA(self) == /\ pc[<<self >>] = "ExA"
             /\ x' = 1
             /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]

B(self,i) == /\ pc[<<self , 1, i>>] = "B"
             /\ x' = x+1
             /\ pc' = [pc EXCEPT ![<<self, 1, i>>] = "EXBB"]

EXBB(self,i) == /\ pc[<<self , 1, i>>] = "EXBB"
                /\ x' = 0
                /\ pc' = [pc EXCEPT ![<<self, 1, i>>] = "Done"]

BX(self,i) == /\ pc[<<self , 2, i>>] = "BX"
              /\ x' = x+1
              /\ pc' = [pc EXCEPT ![<<self, 2, i>>] = "Done"]

p(self) == A(self) \/ ExA(self)

pi1replicate(self, i)  == B(self, i) \/ EXBB(self, i)

pi2replicate(self, i)  == BX(self, i)


D(self) == /\ pc[<<self >>] = "D"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self>>] = "ExD"]

ExD(self) == /\ pc[<<self >>] = "ExD"
             /\ x' = x+1
             /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]

E(self) == /\ pc[<<self , 1>>] = "E"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self, 1>>] = "EXTRA"]

EXTRA(self) == /\ pc[<<self , 1>>] = "EXTRA"
               /\ x' = x+1
               /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]

F(self,i) == /\ pc[<<self , 2, i>>] = "F"
             /\ x' = x+1
             /\ pc' = [pc EXCEPT ![<<self, 2, i>>] = "Done"]

G(self,i) == /\ pc[<<self , 3, i>>] = "G"
             /\ x' = x+1
             /\ pc' = [pc EXCEPT ![<<self, 3, i>>] = "Done"]

q(self) == D(self) \/ ExD(self) \/ E(self) \/ EXTRA(self)

qq1replicate(self, i)  == F(self, i)

qi2replicate(self, i)  == G(self, i)


Next ==    \/ (\E self \in Processes: p(self))
           \/ \E self \in Processes, i \in SubNodes: pi1replicate(self, i)
           \/ \E self \in Processes, i \in 4..5: pi2replicate(self, i)
           \/ (\E self \in ProcessesQ: q(self))
           \/ \E self \in ProcessesQ, i \in SubNodes: qq1replicate(self, i)
           \/ \E self \in ProcessesQ, i \in SubNodes: qi2replicate(self, i)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : \A subprocess \in SubProcSet[self] : WF_vars(p(self))
        /\ \A self \in ProcessesQ : \A subprocess \in SubProcSet[self] : WF_vars(q(self))

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Jun 15 13:32:01 GMT 2022 by zunai
\* Created Tue May 31 09:55:09 GMT 2022 by zunai
