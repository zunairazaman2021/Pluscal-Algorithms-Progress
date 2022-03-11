-------------------------- MODULE SecondBakeryAlgo --------------------------

EXTENDS TLC, Naturals, Integers, Sequences
CONSTANT P, maxticket
ASSUME P \in Nat
Processes == 1..P
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])
(*--algorithm bakeryentrance
variables numbers = [i \in Processes \X {0} |-> 0],
 choosing = [i \in Processes \X {0} |-> FALSE];

define 
  range(val) == {val[i] : i \in DOMAIN val}
  max(val) == CHOOSE v \in range(val) :
                   \A w \in range(val) : w <= v
end define;

fair process bakery \in Processes \X {0}
    begin
    L1: while TRUE do 
          choosing[self] := TRUE;
         
    M:    numbers[self] := 1 + max(numbers);
          choosing[self] := FALSE;
    wait: await  \A j \in Processes \ {self[1]} : pc[self[1],j] = "P2";
    CS:   skip;        
    
    EX:   numbers[self] :=  0; 
        end while;
end process;

fair process  sub \in Processes \X Processes  
      begin
      start:    while TRUE do
                await pc[self[1], 0] = "wait"; 
      L2:       await choosing[self[2], 0] = FALSE;
           
      L3:       await  numbers[self[2], 0] = 0 \/ <<numbers[self[1], 0], self[1]>> \prec <<numbers[self[2], 0], self[2]>>;
      P2:     await  pc[self[1], 0] # "wait" 
             end while;   
             
end process;

end algorithm;*)             
\* BEGIN TRANSLATION (chksum(pcal) = "80d72d49" /\ chksum(tla) = "e0defd2a")
VARIABLES numbers, choosing, pc

(* define statement *)
range(val) == {val[i] : i \in DOMAIN val}
max(val) == CHOOSE v \in range(val) :
                 \A w \in range(val) : w <= v


vars == << numbers, choosing, pc >>

ProcSet == (Processes \X {0}) \cup (Processes \X Processes)

Init == (* Global variables *)
        /\ numbers = [i \in Processes \X {0} |-> 0]
        /\ choosing = [i \in Processes \X {0} |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Processes \X {0} -> "L1"
                                        [] self \in Processes \X Processes -> "start"]

L1(self) == /\ pc[self] = "L1"
            /\ choosing' = [choosing EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "M"]
            /\ UNCHANGED numbers

M(self) == /\ pc[self] = "M"
           /\ numbers' = [numbers EXCEPT ![self] = 1 + max(numbers)]
           /\ choosing' = [choosing EXCEPT ![self] = FALSE]
           /\ pc' = [pc EXCEPT ![self] = "wait"]

wait(self) == /\ pc[self] = "wait"
              /\ \A j \in Processes \ {self[1]} : pc[self[1],j] = "P2"
              /\ pc' = [pc EXCEPT ![self] = "CS"]
              /\ UNCHANGED << numbers, choosing >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "EX"]
            /\ UNCHANGED << numbers, choosing >>

EX(self) == /\ pc[self] = "EX"
            /\ numbers' = [numbers EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "L1"]
            /\ UNCHANGED choosing

bakery(self) == L1(self) \/ M(self) \/ wait(self) \/ CS(self) \/ EX(self)

start(self) == /\ pc[self] = "start"
               /\ pc[self[1], 0] = "wait"
               /\ pc' = [pc EXCEPT ![self] = "L2"]
               /\ UNCHANGED << numbers, choosing >>

L2(self) == /\ pc[self] = "L2"
            /\ choosing[self[2], 0] = FALSE
            /\ pc' = [pc EXCEPT ![self] = "L3"]
            /\ UNCHANGED << numbers, choosing >>

L3(self) == /\ pc[self] = "L3"
            /\ numbers[self[2], 0] = 0 \/ <<numbers[self[1], 0], self[1]>> \prec <<numbers[self[2], 0], self[2]>>
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << numbers, choosing >>

P2(self) == /\ pc[self] = "P2"
            /\ pc[self[1], 0] # "wait"
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << numbers, choosing >>

sub(self) == start(self) \/ L2(self) \/ L3(self) \/ P2(self)

Next == (\E self \in Processes \X {0}: bakery(self))
           \/ (\E self \in Processes \X Processes: sub(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes \X {0} : WF_vars(bakery(self))
        /\ \A self \in Processes \X Processes : WF_vars(sub(self))

\* END TRANSLATION 
StateConstraint == \A i \in Processes : numbers[i, 0] <= maxticket 
MutualExclusion == \A i, j \in Processes : pc[i] = "CS" /\ pc[j] = "CS" => i=j
StarvationFree == \A i \in Processes : []<> (pc[i,0] = "CS")
=============================================================================
\* Modification History
\* Last modified Fri Mar 11 03:03:02 GMT+12:00 2022 by zunai
\* Created Thu Mar 10 08:56:20 GMT+12:00 2022 by zunai
