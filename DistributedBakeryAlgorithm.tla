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
 choosing = [i \in Processes |-> FALSE], procs, procs3;

define {
  range(val) == {val[i] : i \in DOMAIN val}
  max(val) == CHOOSE v \in range(val) :
                   \A w \in range(val) : w <= v
  }

fair process (bakery \in Processes)
    \*Main Thread
    {L1: while (TRUE){
          choosing[self] := TRUE;
    M:  numbers[self] := 1 + max(numbers);
          choosing[self] := FALSE;

    wait: await  \A n \in Processes \ {self} : <<numbers[self], self>> \prec <<numbers[n], n>>;
    CS:   skip;

    EX:   numbers[self] :=  0;
        };\*end while
}
        { \*L2 Thread
        procs := Processes \ {self};
        procs3 := Processes \ {self};
        PreL2: await  pc[self][1] = "wait";
        start: while (procs # {}){
                   L2: with (i \in procs) {
                        await choosing[i] = FALSE;
                        procs := procs \ {i};
                       }; \*end with
               };\*end while
        }
        {\*L3 Thread
        PL3: await  pc[self][1] = "wait";
        L3:  await  pc[self][2] = "L2";
                  with ( i \in procs3){
                       await  numbers[i] = 0 \/ <<numbers[self], self>> \prec <<numbers[i], i>>;
                       procs3 := procs3 \ {i};
                   };
        }
        \*end process
}
***)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-60ec898ffa96ddafd1f439f050b33eb1
CONSTANT defaultInitValue
VARIABLES numbers, choosing, procs, procs3, pc

(* define statement *)
range(val) == {val[i] : i \in DOMAIN val}
max(val) == CHOOSE v \in range(val) :
                 \A w \in range(val) : w <= v


vars == << numbers, choosing, procs, procs3, pc >>

ProcSet == (Processes)

SubProcSet == [_n1 \in ProcSet |-> 1..3]

Init == (* Global variables *)
        /\ numbers = [i \in Processes |-> 0]
        /\ choosing = [i \in Processes |-> FALSE]
        /\ procs = defaultInitValue
        /\ procs3 = defaultInitValue
        /\ pc = [self \in ProcSet |-> <<"L1","Lbl_1","PL3">>]

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
              /\ \A n \in Processes \ {self} : <<numbers[self], self>> \prec <<numbers[n], n>>
              /\ pc' = [pc EXCEPT ![self][1] = "CS"]
              /\ UNCHANGED << numbers, choosing, procs, procs3 >>

CS(self) == /\ pc[self][1]  = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self][1] = "EX"]
            /\ UNCHANGED << numbers, choosing, procs, procs3 >>

EX(self) == /\ pc[self][1]  = "EX"
            /\ numbers' = [numbers EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self][1] = "L1"]
            /\ UNCHANGED << choosing, procs, procs3 >>

Lbl_1(self) == /\ pc[self][2]  = "Lbl_1"
               /\ procs' = Processes \ {self}
               /\ procs3' = Processes \ {self}
               /\ pc' = [pc EXCEPT ![self][2] = "PreL2"]
               /\ UNCHANGED << numbers, choosing >>

PreL2(self) == /\ pc[self][2]  = "PreL2"
               /\ pc[self][1] = "wait"
               /\ pc' = [pc EXCEPT ![self][2] = "start"]
               /\ UNCHANGED << numbers, choosing, procs, procs3 >>

start(self) == /\ pc[self][2]  = "start"
               /\ IF procs # {}
                     THEN /\ pc' = [pc EXCEPT ![self][2] = "L2"]
                     ELSE /\ pc' = [pc EXCEPT ![self][2] = "Done"]
               /\ UNCHANGED << numbers, choosing, procs, procs3 >>

L2(self) == /\ pc[self][2]  = "L2"
            /\ \E i \in procs:
                 /\ choosing[i] = FALSE
                 /\ procs' = procs \ {i}
            /\ pc' = [pc EXCEPT ![self][2] = "start"]
            /\ UNCHANGED << numbers, choosing, procs3 >>

PL3(self) == /\ pc[self][3]  = "PL3"
             /\ pc[self][1] = "wait"
             /\ pc' = [pc EXCEPT ![self][3] = "L3"]
             /\ UNCHANGED << numbers, choosing, procs, procs3 >>

L3(self) == /\ pc[self][3]  = "L3"
            /\ pc[self][2] = "L2"
            /\ \E i \in procs3:
                 /\ numbers[i] = 0 \/ <<numbers[self], self>> \prec <<numbers[i], i>>
                 /\ procs3' = procs3 \ {i}
            /\ pc' = [pc EXCEPT ![self][3] = "Done"]
            /\ UNCHANGED << numbers, choosing, procs >>

bakery(self) == L1(self) \/ M(self) \/ wait(self) \/ CS(self) \/ EX(self) \/ Lbl_1(self)
                   \/ PreL2(self) \/ start(self) \/ L2(self) \/ PL3(self)
                   \/ L3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Processes: bakery(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : \A subprocess \in SubProcSet[self] : WF_vars(bakery(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3f0b52ba785b47fa8f3d7d5503733364
StateConstraint == \A i \in Processes : numbers[i] <= maxticket
MutualExclusion == \A i, j \in Processes : pc[i] = "CS" /\ pc[j] = "CS" => i=j
StarvationFree == \A i \in Processes : []<> (pc[i] = "CS")
=============================================================================
\* Modification History
\* Last modified Tue Mar 29 16:29:24 GMT 2022 by zunai
\* Created Sun Mar 27 13:39:18 GMT 2022 by zunai
