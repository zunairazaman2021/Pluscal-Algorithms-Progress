-------------------------- MODULE SecondBakeryAlgo --------------------------

EXTENDS TLC, Naturals, Integers, Sequences
CONSTANT P, maxticket
ASSUME P \in Nat
Processes == 1..P
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])
(*--algorithm bakeryentrance
variables numbers = [i \in Processes \X {0} |-> 0],
 choosing = [i \in Processes \X {0} |-> FALSE],
  maxret = [x \in Processes \X {0} |-> 0];

define 
  range(val) == {val[i] : i \in DOMAIN val}
  max(val) == CHOOSE v \in range(val) :
                   \A w \in range(val) : w <= v
end define;

procedure maxx()
        variables k=1, m = -1, temp;
        begin 
        max1: while TRUE do 
               max2: temp := numbers[self];
               max3: if temp > m then
                      m := temp;
                    end if;
                    
             end while;             
        max4: maxret[self] := m;
        max5: return;  
    end procedure;


fair process bakery \in Processes \X {0}
    begin
    L1: while TRUE do 
          choosing[self] := TRUE;
          
    M0: call maxx();
    \*By un-commenting the M1, we can observe over system is non-starvation free
    M1: if maxret[self] >= maxticket then
            numbers[self] := maxticket;
            maxret[self] := maxticket - 1;
          end if;
    M3: numbers[self] := 1 + maxret[self];        
             
    MP:     choosing[self] := FALSE;
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
\* BEGIN TRANSLATION (chksum(pcal) = "8293185f" /\ chksum(tla) = "48144e83")
CONSTANT defaultInitValue
VARIABLES numbers, choosing, maxret, pc, stack

(* define statement *)
range(val) == {val[i] : i \in DOMAIN val}
max(val) == CHOOSE v \in range(val) :
                 \A w \in range(val) : w <= v

VARIABLES k, m, temp

vars == << numbers, choosing, maxret, pc, stack, k, m, temp >>

ProcSet == (Processes \X {0}) \cup (Processes \X Processes)

Init == (* Global variables *)
        /\ numbers = [i \in Processes \X {0} |-> 0]
        /\ choosing = [i \in Processes \X {0} |-> FALSE]
        /\ maxret = [x \in Processes \X {0} |-> 0]
        (* Procedure maxx *)
        /\ k = [ self \in ProcSet |-> 1]
        /\ m = [ self \in ProcSet |-> -1]
        /\ temp = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Processes \X {0} -> "L1"
                                        [] self \in Processes \X Processes -> "start"]

max1(self) == /\ pc[self] = "max1"
              /\ pc' = [pc EXCEPT ![self] = "max2"]
              /\ UNCHANGED << numbers, choosing, maxret, stack, k, m, temp >>

max2(self) == /\ pc[self] = "max2"
              /\ temp' = [temp EXCEPT ![self] = numbers[self]]
              /\ pc' = [pc EXCEPT ![self] = "max3"]
              /\ UNCHANGED << numbers, choosing, maxret, stack, k, m >>

max3(self) == /\ pc[self] = "max3"
              /\ IF temp[self] > m[self]
                    THEN /\ m' = [m EXCEPT ![self] = temp[self]]
                    ELSE /\ TRUE
                         /\ m' = m
              /\ pc' = [pc EXCEPT ![self] = "max1"]
              /\ UNCHANGED << numbers, choosing, maxret, stack, k, temp >>

max4(self) == /\ pc[self] = "max4"
              /\ maxret' = [maxret EXCEPT ![self] = m[self]]
              /\ pc' = [pc EXCEPT ![self] = "max5"]
              /\ UNCHANGED << numbers, choosing, stack, k, m, temp >>

max5(self) == /\ pc[self] = "max5"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ k' = [k EXCEPT ![self] = Head(stack[self]).k]
              /\ m' = [m EXCEPT ![self] = Head(stack[self]).m]
              /\ temp' = [temp EXCEPT ![self] = Head(stack[self]).temp]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << numbers, choosing, maxret >>

maxx(self) == max1(self) \/ max2(self) \/ max3(self) \/ max4(self)
                 \/ max5(self)

L1(self) == /\ pc[self] = "L1"
            /\ choosing' = [choosing EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "M0"]
            /\ UNCHANGED << numbers, maxret, stack, k, m, temp >>

M0(self) == /\ pc[self] = "M0"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "maxx",
                                                     pc        |->  "M1",
                                                     k         |->  k[self],
                                                     m         |->  m[self],
                                                     temp      |->  temp[self] ] >>
                                                 \o stack[self]]
            /\ k' = [k EXCEPT ![self] = 1]
            /\ m' = [m EXCEPT ![self] = -1]
            /\ temp' = [temp EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "max1"]
            /\ UNCHANGED << numbers, choosing, maxret >>

M1(self) == /\ pc[self] = "M1"
            /\ IF maxret[self] >= maxticket
                  THEN /\ numbers' = [numbers EXCEPT ![self] = maxticket]
                       /\ maxret' = [maxret EXCEPT ![self] = maxticket - 1]
                  ELSE /\ TRUE
                       /\ UNCHANGED << numbers, maxret >>
            /\ pc' = [pc EXCEPT ![self] = "M3"]
            /\ UNCHANGED << choosing, stack, k, m, temp >>

M3(self) == /\ pc[self] = "M3"
            /\ numbers' = [numbers EXCEPT ![self] = 1 + maxret[self]]
            /\ pc' = [pc EXCEPT ![self] = "MP"]
            /\ UNCHANGED << choosing, maxret, stack, k, m, temp >>

MP(self) == /\ pc[self] = "MP"
            /\ choosing' = [choosing EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "wait"]
            /\ UNCHANGED << numbers, maxret, stack, k, m, temp >>

wait(self) == /\ pc[self] = "wait"
              /\ \A j \in Processes \ {self[1]} : pc[self[1],j] = "P2"
              /\ pc' = [pc EXCEPT ![self] = "CS"]
              /\ UNCHANGED << numbers, choosing, maxret, stack, k, m, temp >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "EX"]
            /\ UNCHANGED << numbers, choosing, maxret, stack, k, m, temp >>

EX(self) == /\ pc[self] = "EX"
            /\ numbers' = [numbers EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "L1"]
            /\ UNCHANGED << choosing, maxret, stack, k, m, temp >>

bakery(self) == L1(self) \/ M0(self) \/ M1(self) \/ M3(self) \/ MP(self)
                   \/ wait(self) \/ CS(self) \/ EX(self)

start(self) == /\ pc[self] = "start"
               /\ pc[self[1], 0] = "wait"
               /\ pc' = [pc EXCEPT ![self] = "L2"]
               /\ UNCHANGED << numbers, choosing, maxret, stack, k, m, temp >>

L2(self) == /\ pc[self] = "L2"
            /\ choosing[self[2], 0] = FALSE
            /\ pc' = [pc EXCEPT ![self] = "L3"]
            /\ UNCHANGED << numbers, choosing, maxret, stack, k, m, temp >>

L3(self) == /\ pc[self] = "L3"
            /\ numbers[self[2], 0] = 0 \/ <<numbers[self[1], 0], self[1]>> \prec <<numbers[self[2], 0], self[2]>>
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << numbers, choosing, maxret, stack, k, m, temp >>

P2(self) == /\ pc[self] = "P2"
            /\ pc[self[1], 0] # "wait"
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << numbers, choosing, maxret, stack, k, m, temp >>

sub(self) == start(self) \/ L2(self) \/ L3(self) \/ P2(self)

Next == (\E self \in ProcSet: maxx(self))
           \/ (\E self \in Processes \X {0}: bakery(self))
           \/ (\E self \in Processes \X Processes: sub(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes \X {0} : WF_vars(bakery(self)) /\ WF_vars(maxx(self))
        /\ \A self \in Processes \X Processes : WF_vars(sub(self))

\* END TRANSLATION 
StateConstraint == \A i \in Processes : numbers[i, 0] <= maxticket 
MutualExclusion ==  \A i, j \in Processes: (i # j) => ~ (pc[i, 0] = "CS" /\ pc[j, 0] = "CS")
StarvationFree == \A i \in Processes : []<> (pc[i,0] = "CS")
=============================================================================
\* Modification History
\* Last modified Sat Mar 12 09:53:29 GMT 2022 by zunai
\* Created Thu Mar 10 08:56:20 GMT+12:00 2022 by zunai
