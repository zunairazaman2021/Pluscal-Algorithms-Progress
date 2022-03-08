-------------------------- MODULE FirstBakeryAlgo --------------------------
EXTENDS TLC, Naturals, Integers, Sequences
CONSTANT P, maxticket
ASSUME P \in Nat
Processes == 1..P
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])
(*--algorithm bakeryentrance
variables numbers = [i \in Processes |-> 0],
 choosing = [i \in Processes |-> FALSE];


define 
  range(val) == {val[i] : i \in DOMAIN val}
  max(val) == CHOOSE v \in range(val) :
                   \A w \in range(val) : w <= v
end define;

fair process bakery \in Processes
    variables k = 1;
    begin
    L1: while TRUE do 
          choosing[self] := TRUE;
         
    M:    numbers[self] := 1 + max(numbers);
          choosing[self] := FALSE;
          k := 1;
    L2:   while k <= P do
            await choosing[k] = FALSE;
            
    L3:      await k = self \/ numbers[k] = 0 \/ <<numbers[self], self>> \prec <<numbers[k], k>>;
             k := k+1
          end while;
    CS:   skip;        
    
    EX:   numbers[self] :=  0; 
        end while;
    end process;


end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "59a32c04" /\ chksum(tla) = "5045958b")
VARIABLES numbers, choosing, pc

(* define statement *)
range(val) == {val[i] : i \in DOMAIN val}
max(val) == CHOOSE v \in range(val) :
                 \A w \in range(val) : w <= v

VARIABLE k

vars == << numbers, choosing, pc, k >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ numbers = [i \in Processes |-> 0]
        /\ choosing = [i \in Processes |-> FALSE]
        (* Process bakery *)
        /\ k = [self \in Processes |-> 1]
        /\ pc = [self \in ProcSet |-> "L1"]

L1(self) == /\ pc[self] = "L1"
            /\ choosing' = [choosing EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "M"]
            /\ UNCHANGED << numbers, k >>

M(self) == /\ pc[self] = "M"
           /\ numbers' = [numbers EXCEPT ![self] = 1 + max(numbers)]
           /\ choosing' = [choosing EXCEPT ![self] = FALSE]
           /\ k' = [k EXCEPT ![self] = 1]
           /\ pc' = [pc EXCEPT ![self] = "L2"]

L2(self) == /\ pc[self] = "L2"
            /\ IF k[self] <= P
                  THEN /\ choosing[k[self]] = FALSE
                       /\ pc' = [pc EXCEPT ![self] = "L3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << numbers, choosing, k >>

L3(self) == /\ pc[self] = "L3"
            /\ k[self] = self \/ numbers[k[self]] = 0 \/ <<numbers[self], self>> \prec <<numbers[k[self]], k[self]>>
            /\ k' = [k EXCEPT ![self] = k[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "L2"]
            /\ UNCHANGED << numbers, choosing >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "EX"]
            /\ UNCHANGED << numbers, choosing, k >>

EX(self) == /\ pc[self] = "EX"
            /\ numbers' = [numbers EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "L1"]
            /\ UNCHANGED << choosing, k >>

bakery(self) == L1(self) \/ M(self) \/ L2(self) \/ L3(self) \/ CS(self)
                   \/ EX(self)

Next == (\E self \in Processes: bakery(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(bakery(self))

\* END TRANSLATION 

StateConstraint == \A i \in Processes : numbers[i] <= maxticket 
MutualExclusion == \A i, j \in Processes : pc[i] = "CS" /\ pc[j] = "CS" => i=j
StarvationFree == \A i \in Processes : []<> (pc[i] = "CS")
=============================================================================
\* Modification History
\* Last modified Wed Mar 09 04:48:06 GMT+12:00 2022 by zunai
\* Created Tue Mar 08 23:54:26 GMT+12:00 2022 by zunai
