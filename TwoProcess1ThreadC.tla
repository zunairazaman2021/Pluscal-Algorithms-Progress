------------------------- MODULE TwoProcess1ThreadC -------------------------

EXTENDS Naturals, TLC

\* CONSTANT N           (* Size of arrays *)
N == 2
\* CONSTANT MAXINT      (* Size of arrays *)
MAXINT == 3
\* CONSTANT PROCSet     (* Set of process indexes *)
PROCSet == 1 .. 2     (* Set of process indexes *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid1 \in PROCSet )
{
    One:
        found := TRUE;
      Two:
                i := i + 1;
}
{ Z: 
    i := i + 1;
}

process ( pid2 \in 4..5 )
{
    Three:
                x := ar[1];
      Four:
                ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "28c34502" /\ chksum(tla) = "745f38eb")
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == (PROCSet) \cup (4..5)

Genprocs1 == { <<p>>: p \in PROCSet }

Genprocs1Thread1 == { <<p,1>>: p \in PROCSet }

Genprocs2 == { <<p>>: p \in 4..5 }

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in PROCSet THEN 1..2
                                 ELSE (**4..5**) 1..1]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in Genprocs1 \union Genprocs1Thread1 \union Genprocs2 |-> CASE  self \in Genprocs1 -> "One"
		 [] self \in Genprocs1Thread1 -> "Z"
		 [] self \in Genprocs2 -> "Three" ]

One(self) == /\ pc[<<self >>] = "One"
             /\ found' = TRUE
             /\ pc' = [pc EXCEPT ![<<self>>] = "Two"]
             /\ UNCHANGED << ar, x, i >>

Two(self) == /\ pc[<<self >>] = "Two"
             /\ i' = i + 1
             /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]
             /\ UNCHANGED << ar, x, found >>

Z(self) == /\ pc[<<self , 1>>] = "Z"
           /\ i' = i + 1
           /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]
           /\ UNCHANGED << ar, x, found >>

pid1(self) == One(self) \/ Two(self)

pid1sub1(self)  == Z(self)


Three(self) == /\ pc[<<self >>] = "Three"
               /\ x' = ar[1]
               /\ pc' = [pc EXCEPT ![<<self>>] = "Four"]
               /\ UNCHANGED << ar, found, i >>

Four(self) == /\ pc[<<self >>] = "Four"
              /\ ar' = [ar EXCEPT ![i] = 0]
              /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]
              /\ UNCHANGED << x, found, i >>

pid2(self) == Three(self) \/ Four(self)


Next ==    \/ (\E self \in PROCSet: pid1(self))
           \/ \E self \in PROCSet: pid1sub1(self)
           \/ (\E self \in 4..5: pid2(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCSet : WF_vars(pid1(self))
        /\ \A self \in 4..5 : WF_vars(pid2(self))

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Jun 24 10:28:47 GMT 2022 by zunai
\* Created Fri Jun 24 10:26:14 GMT 2022 by zunai
