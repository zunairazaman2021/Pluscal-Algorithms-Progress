-------------------------- MODULE FinalBakeryAlgo --------------------------
EXTENDS TLC, Naturals, Integers, Sequences
CONSTANT P, maxticket, maxlength
ASSUME P \in Nat
Processes == 1..P
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])
(* PlusCal options (-distpcal) *)
(***
--algorithm bakeryentrance{
variables numbers = [i \in Processes |-> 0],
          localNum = [j \in Processes, i \in Processes |-> 0],
          localCh = [j \in Processes, i \in Processes |-> FALSE],
          ackRcvd = [i \in Processes, j \in Processes |-> FALSE];
fifos network[Processes,Processes];

define {
  range(val) == {val[i] : i \in DOMAIN val}
  max(val) == CHOOSE v \in range(val) :
                   \A w \in range(val) : w <= v
  \* messages used in the algorithm
     Request(c) == [type |-> "request", numbers |-> c]
     Release(c) == [type |-> "release", numbers |-> c]
     Acknowledge == [type |-> "ack"]
  }

fair process (bakery \in Processes)
    \*Main Thread
    variables  procs0 =Processes \ {self},procs1 =Processes \ {self},procs =Processes \ {self}, procs3 =Processes \ {self}, msg, sndr;
   {L1: while (TRUE){

    IS: await pc[self][2] = "XL" /\ pc[self][4] = "PreL2" /\ pc[self][5] = "PreL3" ;

    M:   await procs0={};
        numbers[self] := 1 + max([j \in Processes \{self} |-> localNum[self, j]]);
        multicast(network, [self, i \in Processes |-> Request(numbers[self])]);
    PreWait: await pc[self][3] = "PL0" /\ pc[self][4] = "PreL2" /\ pc[self][5] = "PreL3" ;
    wait: await procs3 = {};
    CS:   skip;
          numbers[self] :=  0;
         \* await pc[self][6] = "EX";
          ackRcvd := [i,j \in Processes |-> IF i=self THEN FALSE ELSE ackRcvd[i,j]];
          multicast(network, [self, n \in Processes \ {self} |-> Release(0)]);
           };\*end while
      }
     {\*Second XL Thread
      XL: while(TRUE){
        await  pc[self][1] = "M";
       XL1:  while (procs0 # {}){
           with (j \in procs0){
             localCh[j, self] := TRUE;
             procs0 := procs0 \ {j};
          };
          };
         POSTXL: await pc[self][1] # "M";
          };
      }
      {\*L0 Thread
      PL0: while (TRUE){
            await pc[self][1] = "wait";
      L0: while(procs1 # {}){
                  with (j \in procs1){
                       await ackRcvd[self, j] = TRUE;
                             localCh[j, self] := FALSE;
                       procs1 := procs1 \ {j};
                  };
      };
      PostL0: await pc[self][1] # "wait";
         procs1 := Processes \ {self};
      };
      }

     { \*L2 Thread
        PreL2:while (TRUE){
               await  pc[self][1] = "wait";
        L2:      while (procs # {}){
                  with (j \in procs \ procs1){
                        await localCh[self,j] = FALSE;
                        procs := procs \ {j};
                       }; \*end with
               };\*end while
        POSTL2: await pc[self][1] # "wait";
         procs := Processes \ {self};
        }; \*end while
        }
        {\*L3 Thread
        PreL3: while (TRUE){
             await  pc[self][1] = "wait";
        L3:    while (procs3 # {}){
              with ( j \in procs3 \ procs){
                   await  localNum[self, j] = 0 \/ <<numbers[self], self>> \prec <<localNum[self, j], j>>;
                   procs3 := procs3 \ {j};
                   };
            };\*end while

        POSTL3: await pc[self][1] # "wait";
         procs3 := Processes \ {self};
        }; \*end while
        }
        {\*Message Handling Thread
        RCV: while (TRUE) {
               with (j \in Processes){
                 await network[j, self] # <<>>;
                 receive(network[j,self], msg);
                 sndr := j;
               };
        HANDLE:  if (msg.type = "ack"){
                  ackRcvd[self, sndr] := TRUE;
                  }
                 else if(msg.type = "request"){
                    localNum[self, sndr] := msg.numbers;
                    send(network[self, sndr], Acknowledge);
                 } else if(msg.type = "release"){
                   send(network[self, sndr], Release(0));
                 }
        };\*end while
        }
(*
      { EX: while(TRUE){
        await  pc[self][1] = "CS";
       EX1: with (j \in Processes){
          ackRcvd[self,j] := FALSE;
          };
          };
      }
*)
}
***)




\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e5f2a5fdb21889306eb101e492ae82bc
CONSTANT defaultInitValue
VARIABLES numbers, localNum, localCh, ackRcvd, network, pc

(* define statement *)
range(val) == {val[i] : i \in DOMAIN val}
max(val) == CHOOSE v \in range(val) :
                 \A w \in range(val) : w <= v

   Request(c) == [type |-> "request", numbers |-> c]
   Release(c) == [type |-> "release", numbers |-> c]
   Acknowledge == [type |-> "ack"]

VARIABLES procs0, procs1, procs, procs3, msg, sndr

vars == << numbers, localNum, localCh, ackRcvd, network, pc, procs0, procs1, 
           procs, procs3, msg, sndr >>

ProcSet == (Processes)

SubProcSet == [_n1 \in ProcSet |-> 1..6]

Init == (* Global variables *)
        /\ numbers = [i \in Processes |-> 0]
        /\ localNum = [j \in Processes, i \in Processes |-> 0]
        /\ localCh = [j \in Processes, i \in Processes |-> FALSE]
        /\ ackRcvd = [i \in Processes, j \in Processes |-> FALSE]
        /\ network = [_n20 \in Processes, _n31 \in Processes |-> <<>>]
        (* Process bakery *)
        /\ procs0 = [self \in Processes |-> Processes \ {self}]
        /\ procs1 = [self \in Processes |-> Processes \ {self}]
        /\ procs = [self \in Processes |-> Processes \ {self}]
        /\ procs3 = [self \in Processes |-> Processes \ {self}]
        /\ msg = [self \in Processes |-> defaultInitValue]
        /\ sndr = [self \in Processes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> <<"L1","XL","PL0","PreL2","PreL3","RCV">>]

L1(self) == /\ pc[self][1]  = "L1"
            /\ pc' = [pc EXCEPT ![self][1] = "IS"]
            /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                            procs0, procs1, procs, procs3, msg, sndr >>

IS(self) == /\ pc[self][1]  = "IS"
            /\ pc[self][2] = "XL" /\ pc[self][4] = "PreL2" /\ pc[self][5] = "PreL3"
            /\ pc' = [pc EXCEPT ![self][1] = "M"]
            /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                            procs0, procs1, procs, procs3, msg, sndr >>

M(self) == /\ pc[self][1]  = "M"
           /\ procs0[self]={}
           /\ numbers' = [numbers EXCEPT ![self] = 1 + max([j \in Processes \{self} |-> localNum[self, j]])]
           /\ network' = [<<slf, i>> \in DOMAIN network |->  IF slf = self 
                          /\ i \in Processes THEN 
                          Append(network[slf, i], Request(numbers'[self])) ELSE network[slf, i]]
           /\ pc' = [pc EXCEPT ![self][1] = "PreWait"]
           /\ UNCHANGED << localNum, localCh, ackRcvd, procs0, procs1, procs, 
                           procs3, msg, sndr >>

PreWait(self) == /\ pc[self][1]  = "PreWait"
                 /\ pc[self][3] = "PL0" /\ pc[self][4] = "PreL2" /\ pc[self][5] = "PreL3"
                 /\ pc' = [pc EXCEPT ![self][1] = "wait"]
                 /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                                 procs0, procs1, procs, procs3, msg, sndr >>

wait(self) == /\ pc[self][1]  = "wait"
              /\ procs3[self] = {}
              /\ pc' = [pc EXCEPT ![self][1] = "CS"]
              /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                              procs0, procs1, procs, procs3, msg, sndr >>

CS(self) == /\ pc[self][1]  = "CS"
            /\ TRUE
            /\ numbers' = [numbers EXCEPT ![self] = 0]
            /\ ackRcvd' = [i,j \in Processes |-> IF i=self THEN FALSE ELSE ackRcvd[i,j]]
            /\ network' = [<<slf, n>> \in DOMAIN network |->  IF slf = self 
                           /\ n \in Processes \ { self } THEN 
                           Append(network[slf, n], Release(0)) ELSE network[slf, n]]
            /\ pc' = [pc EXCEPT ![self][1] = "L1"]
            /\ UNCHANGED << localNum, localCh, procs0, procs1, procs, procs3, 
                            msg, sndr >>

XL(self) == /\ pc[self][2]  = "XL"
            /\ pc[self][1] = "M"
            /\ pc' = [pc EXCEPT ![self][2] = "XL1"]
            /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                            procs0, procs1, procs, procs3, msg, sndr >>

XL1(self) == /\ pc[self][2]  = "XL1"
             /\ IF procs0[self] # {}
                   THEN /\ \E j \in procs0[self]:
                             /\ localCh' = [localCh EXCEPT ![j, self] = TRUE]
                             /\ procs0' = [procs0 EXCEPT ![self] = procs0[self] \ {j}]
                        /\ pc' = [pc EXCEPT ![self][2] = "XL1"]
                   ELSE /\ pc' = [pc EXCEPT ![self][2] = "POSTXL"]
                        /\ UNCHANGED << localCh, procs0 >>
             /\ UNCHANGED << numbers, localNum, ackRcvd, network, procs1, 
                             procs, procs3, msg, sndr >>

POSTXL(self) == /\ pc[self][2]  = "POSTXL"
                /\ pc[self][1] # "M"
                /\ pc' = [pc EXCEPT ![self][2] = "XL"]
                /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                                procs0, procs1, procs, procs3, msg, sndr >>

PL0(self) == /\ pc[self][3]  = "PL0"
             /\ pc[self][1] = "wait"
             /\ pc' = [pc EXCEPT ![self][3] = "L0"]
             /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                             procs0, procs1, procs, procs3, msg, sndr >>

L0(self) == /\ pc[self][3]  = "L0"
            /\ IF procs1[self] # {}
                  THEN /\ \E j \in procs1[self]:
                            /\ ackRcvd[self, j] = TRUE
                            /\ localCh' = [localCh EXCEPT ![j, self] = FALSE]
                            /\ procs1' = [procs1 EXCEPT ![self] = procs1[self] \ {j}]
                       /\ pc' = [pc EXCEPT ![self][3] = "L0"]
                  ELSE /\ pc' = [pc EXCEPT ![self][3] = "PostL0"]
                       /\ UNCHANGED << localCh, procs1 >>
            /\ UNCHANGED << numbers, localNum, ackRcvd, network, procs0, procs, 
                            procs3, msg, sndr >>

PostL0(self) == /\ pc[self][3]  = "PostL0"
                /\ pc[self][1] # "wait"
                /\ procs1' = [procs1 EXCEPT ![self] = Processes \ {self}]
                /\ pc' = [pc EXCEPT ![self][3] = "PL0"]
                /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                                procs0, procs, procs3, msg, sndr >>

PreL2(self) == /\ pc[self][4]  = "PreL2"
               /\ pc[self][1] = "wait"
               /\ pc' = [pc EXCEPT ![self][4] = "L2"]
               /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                               procs0, procs1, procs, procs3, msg, sndr >>

L2(self) == /\ pc[self][4]  = "L2"
            /\ IF procs[self] # {}
                  THEN /\ \E j \in procs[self] \ procs1[self]:
                            /\ localCh[self,j] = FALSE
                            /\ procs' = [procs EXCEPT ![self] = procs[self] \ {j}]
                       /\ pc' = [pc EXCEPT ![self][4] = "L2"]
                  ELSE /\ pc' = [pc EXCEPT ![self][4] = "POSTL2"]
                       /\ procs' = procs
            /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                            procs0, procs1, procs3, msg, sndr >>

POSTL2(self) == /\ pc[self][4]  = "POSTL2"
                /\ pc[self][1] # "wait"
                /\ procs' = [procs EXCEPT ![self] = Processes \ {self}]
                /\ pc' = [pc EXCEPT ![self][4] = "PreL2"]
                /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                                procs0, procs1, procs3, msg, sndr >>

PreL3(self) == /\ pc[self][5]  = "PreL3"
               /\ pc[self][1] = "wait"
               /\ pc' = [pc EXCEPT ![self][5] = "L3"]
               /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                               procs0, procs1, procs, procs3, msg, sndr >>

L3(self) == /\ pc[self][5]  = "L3"
            /\ IF procs3[self] # {}
                  THEN /\ \E j \in procs3[self] \ procs[self]:
                            /\ localNum[self, j] = 0 \/ <<numbers[self], self>> \prec <<localNum[self, j], j>>
                            /\ procs3' = [procs3 EXCEPT ![self] = procs3[self] \ {j}]
                       /\ pc' = [pc EXCEPT ![self][5] = "L3"]
                  ELSE /\ pc' = [pc EXCEPT ![self][5] = "POSTL3"]
                       /\ UNCHANGED procs3
            /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                            procs0, procs1, procs, msg, sndr >>

POSTL3(self) == /\ pc[self][5]  = "POSTL3"
                /\ pc[self][1] # "wait"
                /\ procs3' = [procs3 EXCEPT ![self] = Processes \ {self}]
                /\ pc' = [pc EXCEPT ![self][5] = "PreL3"]
                /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, network, 
                                procs0, procs1, procs, msg, sndr >>

RCV(self) == /\ pc[self][6]  = "RCV"
             /\ \E j \in Processes:
                  /\ network[j, self] # <<>>
                  /\ Len(network[j,self]) > 0 
                  /\ msg' = [msg EXCEPT ![self] = Head(network[j,self])]
                  /\ network' = [network EXCEPT ![j,self] =  Tail(@) ]
                  /\ sndr' = [sndr EXCEPT ![self] = j]
             /\ pc' = [pc EXCEPT ![self][6] = "HANDLE"]
             /\ UNCHANGED << numbers, localNum, localCh, ackRcvd, procs0, 
                             procs1, procs, procs3 >>

HANDLE(self) == /\ pc[self][6]  = "HANDLE"
                /\ IF msg[self].type = "ack"
                      THEN /\ ackRcvd' = [ackRcvd EXCEPT ![self, sndr[self]] = TRUE]
                           /\ UNCHANGED << localNum, network >>
                      ELSE /\ IF msg[self].type = "request"
                                 THEN /\ localNum' = [localNum EXCEPT ![self, sndr[self]] = msg[self].numbers]
                                      /\ network' = [network EXCEPT ![self, sndr[self]] =  Append(@, Acknowledge)]
                                 ELSE /\ IF msg[self].type = "release"
                                            THEN /\ network' = [network EXCEPT ![self, sndr[self]] =  Append(@, Release(0))]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED network
                                      /\ UNCHANGED localNum
                           /\ UNCHANGED ackRcvd
                /\ pc' = [pc EXCEPT ![self][6] = "RCV"]
                /\ UNCHANGED << numbers, localCh, procs0, procs1, procs, 
                                procs3, msg, sndr >>

bakery(self) == L1(self) \/ IS(self) \/ M(self) \/ PreWait(self)
                   \/ wait(self) \/ CS(self) \/ XL(self) \/ XL1(self)
                   \/ POSTXL(self) \/ PL0(self) \/ L0(self) \/ PostL0(self) \/ PreL2(self)
                   \/ L2(self) \/ POSTL2(self) \/ PreL3(self) \/ L3(self)
                   \/ POSTL3(self) \/ RCV(self) \/ HANDLE(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Processes: bakery(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : \A subprocess \in SubProcSet[self] : WF_vars(bakery(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-82958fdf515ad49cfabd0e33c914c616
StateConstraint == 
  /\ \A i \in Processes : numbers[i] <= maxticket 
  /\ \A i, j \in Processes: Len(network[i,j]) <= maxlength

MutualExclusion == \A i, j \in Processes : pc[i][1] = "CS" /\ pc[j][1] = "CS"  => i=j
StarvationFree == \A proc \in Processes : (pc[proc][1] = "wait") ~> (pc[proc][1] = "CS")

=============================================================================
\* Modification History
\* Last modified Wed Apr 13 15:13:53 GMT 2022 by zunai
\* Created Sun Mar 27 13:39:18 GMT 2022 by zunai
