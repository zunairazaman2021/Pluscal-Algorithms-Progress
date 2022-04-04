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
    PreWait: await pc[self][2] = "L2" /\ pc[self][3] = "L3";
    wait: await procs3 = {};
    CS:   skip;
          numbers[self] :=  0;
           };\*end while
}
     { \*L2 Thread
        PreL2:while (TRUE){
               await  pc[self][1] = "wait";
               procs := Processes \ {self};
        L2:      while (procs # {}){
                  with (i \in procs){
                        await choosing[i] = FALSE;
                        procs := procs \ {i};
                       }; \*end with
               };\*end while
        }; \*end while
        POSTL2: await pc[self][1] # "wait";

        }
        {\*L3 Thread
        PreL3: while (TRUE){
             await  pc[self][1] = "wait";
             procs3 := Processes \ {self};
        L3:    while (procs3 # {}){
              with ( i \in procs3 \ procs){
                   await  numbers[i] = 0 \/ <<numbers[self], self>> \prec <<numbers[i], i>>;
                   procs3 := procs3 \ {i};
                   };
            };\*end while
        }; \*end while
        POSTL3: await pc[self][1] # "wait";

        }
}
***)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-581e8653d97451627f5529def049d7b9
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
        /\ pc = [self \in ProcSet |-> <<"L1","PreL2","PreL3">>]

L1(self) == /\ pc[self][1]  = "L1"
            /\ choosing' = [choosing EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self][1] = "M"]
            /\ UNCHANGED << numbers, procs, procs3 >>

M(self) == /\ pc[self][1]  = "M"
           /\ numbers' = [numbers EXCEPT ![self] = 1 + max(numbers)]
           /\ choosing' = [choosing EXCEPT ![self] = FALSE]
           /\ pc' = [pc EXCEPT ![self][1] = "PreWait"]
           /\ UNCHANGED << procs, procs3 >>

PreWait(self) == /\ pc[self][1]  = "PreWait"
                 /\ pc[self][2] = "L2" /\ pc[self][3] = "L3"
                 /\ pc' = [pc EXCEPT ![self][1] = "wait"]
                 /\ UNCHANGED << numbers, choosing, procs, procs3 >>

wait(self) == /\ pc[self][1]  = "wait"
              /\ procs3[self] = {}
              /\ pc' = [pc EXCEPT ![self][1] = "CS"]
              /\ UNCHANGED << numbers, choosing, procs, procs3 >>

CS(self) == /\ pc[self][1]  = "CS"
            /\ TRUE
            /\ numbers' = [numbers EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self][1] = "L1"]
            /\ UNCHANGED << choosing, procs, procs3 >>

PreL2(self) == /\ pc[self][2]  = "PreL2"
               /\ pc[self][1] = "wait"
               /\ procs' = [procs EXCEPT ![self] = Processes \ {self}]
               /\ pc' = [pc EXCEPT ![self][2] = "L2"]
               /\ UNCHANGED << numbers, choosing, procs3 >>

L2(self) == /\ pc[self][2]  = "L2"
            /\ IF procs[self] # {}
                  THEN /\ \E i \in procs[self]:
                            /\ choosing[i] = FALSE
                            /\ procs' = [procs EXCEPT ![self] = procs[self] \ {i}]
                       /\ pc' = [pc EXCEPT ![self][2] = "L2"]
                  ELSE /\ pc' = [pc EXCEPT ![self][2] = "PreL2"]
                       /\ procs' = procs
            /\ UNCHANGED << numbers, choosing, procs3 >>

POSTL2(self) == /\ pc[self][2]  = "POSTL2"
                /\ pc[self][1] # "wait"
                /\ pc' = [pc EXCEPT ![self][2] = "Done"]
                /\ UNCHANGED << numbers, choosing, procs, procs3 >>

PreL3(self) == /\ pc[self][3]  = "PreL3"
               /\ pc[self][1] = "wait"
               /\ procs3' = [procs3 EXCEPT ![self] = Processes \ {self}]
               /\ pc' = [pc EXCEPT ![self][3] = "L3"]
               /\ UNCHANGED << numbers, choosing, procs >>

L3(self) == /\ pc[self][3]  = "L3"
            /\ IF procs3[self] # {}
                  THEN /\ \E i \in procs3[self] \ procs[self]:
                            /\ numbers[i] = 0 \/ <<numbers[self], self>> \prec <<numbers[i], i>>
                            /\ procs3' = [procs3 EXCEPT ![self] = procs3[self] \ {i}]
                       /\ pc' = [pc EXCEPT ![self][3] = "L3"]
                  ELSE /\ pc' = [pc EXCEPT ![self][3] = "PreL3"]
                       /\ UNCHANGED procs3
            /\ UNCHANGED << numbers, choosing, procs >>

POSTL3(self) == /\ pc[self][3]  = "POSTL3"
                /\ pc[self][1] # "wait"
                /\ pc' = [pc EXCEPT ![self][3] = "Done"]
                /\ UNCHANGED << numbers, choosing, procs, procs3 >>

bakery(self) == L1(self) \/ M(self) \/ PreWait(self) \/ wait(self)
                   \/ CS(self) \/ PreL2(self) \/ L2(self) \/ POSTL2(self) \/ PreL3(self)
                   \/ L3(self) \/ POSTL3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Processes: bakery(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : \A subprocess \in SubProcSet[self] : WF_vars(bakery(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-6e663469f11287c1046128e1c6c4986e
StateConstraint == \A i \in Processes : numbers[i] <= maxticket
MutualExclusion == \A i, j \in Processes : pc[i][1] = "CS" /\ pc[j][1] = "CS"  => i=j
StarvationFree == \A proc \in Processes : (pc[proc][1] = "wait") ~> (pc[proc][1] = "CS")

=============================================================================
\* Modification History
\* Last modified Mon Apr 04 12:26:55 GMT 2022 by zunai
\* Created Sun Mar 27 13:39:18 GMT 2022 by zunai
