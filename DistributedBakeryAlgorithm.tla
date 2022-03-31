--------------------- MODULE DistributedBakeryAlgorithm ---------------------

EXTENDS TLC, Naturals, Integers, Sequences
CONSTANT P, maxticket
ASSUME P \in Nat
Processes == 1..P
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

(* PlusCal options (-distpcal) *)
(***
--algorithm bakeryentrance{
variables numbers = [i \in Processes |-> 0],
 choosing = [i \in Processes |-> FALSE];

define {
  range(val) == {val[i] : i \in DOMAIN val}
  max(val) == CHOOSE v \in range(val) :
                   \A w \in range(val) : w <= v
  }

fair process (bakery \in Processes)
    \*Main Thread
    variables  procs ={}, procs3 ={};
    {L1: while (TRUE){
          choosing[self] := TRUE;
    M:  numbers[self] := 1 + max(numbers);
          choosing[self] := FALSE;
    wait: await procs3 = {};
    CS:   skip;
          numbers[self] :=  0;
           };\*end while
}
     { \*L2 Thread
        L2:while (TRUE){
               await  pc[self][1] = "wait";
               procs := Processes \ {self};
              while (procs # {}){
                  with (i \in procs){
                        await choosing[i] = FALSE;
                        procs := procs \ {i};
                       }; \*end with
               };\*end while
        }; \*end while
        }
        {\*L3 Thread
        L3: while (TRUE){
             await  pc[self][1] = "wait";
             procs3 := Processes \ {self};
            while (procs3 # {}){
              with ( i \in procs3 \ procs){
                   await  numbers[i] = 0 \/ <<numbers[self], self>> \prec <<numbers[i], i>>;
                   procs3 := procs3 \ {i};
                   };
            };\*end while
        }; \*end while
        }
}
***)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-05bceeb6b4c3ff794f2cb62760cc28e2
VARIABLES numbers, choosing, pc

(* define statement *)
range(val) == {val[i] : i \in DOMAIN val}
max(val) == CHOOSE v \in range(val) :
                 \A w \in range(val) : w <= v

VARIABLES procs, procs3

vars == << numbers, choosing, pc, procs, procs3 >>

ProcSet == (Processes)

SubProcSet == [_n1 \in ProcSet |-> 1..3]

Init == (* Global variables *)
        /\ numbers = [i \in Processes |-> 0]
        /\ choosing = [i \in Processes |-> FALSE]
        (* Process bakery *)
        /\ procs = [self \in Processes |-> {}]
        /\ procs3 = [self \in Processes |-> {}]
        /\ pc = [self \in ProcSet |-> <<"L1","L2","L3">>]

L1(self) == /\ pc[self][1]  = "L1"
            /\ choosing' = [choosing EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self][1] = "M"]
            /\ UNCHANGED << numbers, procs, procs3 >>

M(self) == /\ pc[self][1]  = "M"
           /\ numbers' = [numbers EXCEPT ![self] = 1 + max(numbers)]
           /\ choosing' = [choosing EXCEPT ![self] = FALSE]
           /\ pc' = [pc EXCEPT ![self][1] = "wait"]
           /\ UNCHANGED << procs, procs3 >>

wait(self) == /\ pc[self][1]  = "wait"
              /\ procs3[self] = {}
              /\ pc' = [pc EXCEPT ![self][1] = "CS"]
              /\ UNCHANGED << numbers, choosing, procs, procs3 >>

CS(self) == /\ pc[self][1]  = "CS"
            /\ TRUE
            /\ numbers' = [numbers EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self][1] = "L1"]
            /\ UNCHANGED << choosing, procs, procs3 >>

L2(self) == /\ pc[self][2]  = "L2"
            /\ pc[self][1] = "wait"
            /\ procs' = [procs EXCEPT ![self] = Processes \ {self}]
            /\ pc' = [pc EXCEPT ![self][2] = "Lbl_1"]
            /\ UNCHANGED << numbers, choosing, procs3 >>

Lbl_1(self) == /\ pc[self][2]  = "Lbl_1"
               /\ IF procs[self] # {}
                     THEN /\ \E i \in procs[self]:
                               /\ choosing[i] = FALSE
                               /\ procs' = [procs EXCEPT ![self] = procs[self] \ {i}]
                          /\ pc' = [pc EXCEPT ![self][2] = "Lbl_1"]
                     ELSE /\ pc' = [pc EXCEPT ![self][2] = "L2"]
                          /\ procs' = procs
               /\ UNCHANGED << numbers, choosing, procs3 >>

L3(self) == /\ pc[self][3]  = "L3"
            /\ pc[self][1] = "wait"
            /\ procs3' = [procs3 EXCEPT ![self] = Processes \ {self}]
            /\ pc' = [pc EXCEPT ![self][3] = "Lbl_2"]
            /\ UNCHANGED << numbers, choosing, procs >>

Lbl_2(self) == /\ pc[self][3]  = "Lbl_2"
               /\ IF procs3[self] # {}
                     THEN /\ \E i \in procs3[self] \ procs[self]:
                               /\ numbers[i] = 0 \/ <<numbers[self], self>> \prec <<numbers[i], i>>
                               /\ procs3' = [procs3 EXCEPT ![self] = procs3[self] \ {i}]
                          /\ pc' = [pc EXCEPT ![self][3] = "Lbl_2"]
                     ELSE /\ pc' = [pc EXCEPT ![self][3] = "L3"]
                          /\ UNCHANGED procs3
               /\ UNCHANGED << numbers, choosing, procs >>

bakery(self) == L1(self) \/ M(self) \/ wait(self) \/ CS(self) \/ L2(self)
                   \/ Lbl_1(self) \/ L3(self) \/ Lbl_2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Processes: bakery(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : \A subprocess \in SubProcSet[self] : WF_vars(bakery(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ecc7a8365ad0a095ad0a83b73f7a6a2c
StateConstraint == \A i \in Processes : numbers[i] <= maxticket
MutualExclusion == \A i, j, n \in Processes : pc[i][1] = "CS" /\ pc[j][2] = "CS" /\ pc[n][3] = "CS" => i=j /\ j=n
StarvationFree == \A proc \in Processes : (pc[proc] = "wait") ~> (pc[proc] = "CS")

=============================================================================
\* Modification History
\* Last modified Thu Mar 31 11:32:15 GMT 2022 by zunai
\* Created Sun Mar 27 13:39:18 GMT 2022 by zunai
