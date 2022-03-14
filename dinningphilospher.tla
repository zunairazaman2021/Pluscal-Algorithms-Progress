------------------------- MODULE dinningphilospher -------------------------
EXTENDS Naturals
CONSTANT N
ASSUME N \in Nat
Procs == 0..N-1

(*--algorithm dinninground
variables fork = [k \in Procs |-> N];
define 
forkAvailable(i) == fork[i] = N
LeftF(i) == i
LeftP(i) == IF i = N-1 THEN 0 ELSE i+1
RightF(i) == IF i=0 THEN N-1 ELSE i-1
RightP(i) == IF i=0 THEN N-1 ELSE i-1
end define;
fair process j \in Procs
variables state = "Thinking";
begin
J0: while TRUE do
    HUNGRY: either if state = "Thinking" then 
                 state := "Hungry";
               end if;  
    or P: if state = "Hungry" /\ self#0 then \* Deadlock eliminated by adding elseif and self#0 
             await forkAvailable(RightF(self));
             fork[RightF(self)] := self;
       EATING: await forkAvailable(LeftF(self));
             fork[LeftF(self)] := self;
             state := "Eating" 
          \*If process is zero, assign it left fork
          elsif state = "Hungry" /\ self=0 then
                  await forkAvailable(LeftF(self));
                  fork[LeftF(self)] := self;
        EATING0: await forkAvailable(RightF(self));
                 fork[RightF(self)] := self;
                 state := "Eating";   
          end if;
      or THINKING: if state = "Eating" then
               state := "Thinking";
               fork[LeftF(self)] := N;
            R: fork[RightF(self)] := N;   
            end if;    
      end either;
       
end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "568f43c" /\ chksum(tla) = "890e6e08")
VARIABLES fork, pc

(* define statement *)
forkAvailable(i) == fork[i] = N
LeftF(i) == i
LeftP(i) == IF i = N-1 THEN 0 ELSE i+1
RightF(i) == IF i=0 THEN N-1 ELSE i-1
RightP(i) == IF i=0 THEN N-1 ELSE i-1

VARIABLE state

vars == << fork, pc, state >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ fork = [k \in Procs |-> N]
        (* Process j *)
        /\ state = [self \in Procs |-> "Thinking"]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ pc' = [pc EXCEPT ![self] = "HUNGRY"]
            /\ UNCHANGED << fork, state >>

HUNGRY(self) == /\ pc[self] = "HUNGRY"
                /\ \/ /\ IF state[self] = "Thinking"
                            THEN /\ state' = [state EXCEPT ![self] = "Hungry"]
                            ELSE /\ TRUE
                                 /\ state' = state
                      /\ pc' = [pc EXCEPT ![self] = "J0"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "P"]
                      /\ state' = state
                   \/ /\ pc' = [pc EXCEPT ![self] = "THINKING"]
                      /\ state' = state
                /\ fork' = fork

P(self) == /\ pc[self] = "P"
           /\ IF state[self] = "Hungry" /\ self#0
                 THEN /\ forkAvailable(RightF(self))
                      /\ fork' = [fork EXCEPT ![RightF(self)] = self]
                      /\ pc' = [pc EXCEPT ![self] = "EATING"]
                 ELSE /\ IF state[self] = "Hungry" /\ self=0
                            THEN /\ forkAvailable(LeftF(self))
                                 /\ fork' = [fork EXCEPT ![LeftF(self)] = self]
                                 /\ pc' = [pc EXCEPT ![self] = "EATING0"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "J0"]
                                 /\ fork' = fork
           /\ state' = state

EATING(self) == /\ pc[self] = "EATING"
                /\ forkAvailable(LeftF(self))
                /\ fork' = [fork EXCEPT ![LeftF(self)] = self]
                /\ state' = [state EXCEPT ![self] = "Eating"]
                /\ pc' = [pc EXCEPT ![self] = "J0"]

EATING0(self) == /\ pc[self] = "EATING0"
                 /\ forkAvailable(RightF(self))
                 /\ fork' = [fork EXCEPT ![RightF(self)] = self]
                 /\ state' = [state EXCEPT ![self] = "Eating"]
                 /\ pc' = [pc EXCEPT ![self] = "J0"]

THINKING(self) == /\ pc[self] = "THINKING"
                  /\ IF state[self] = "Eating"
                        THEN /\ state' = [state EXCEPT ![self] = "Thinking"]
                             /\ fork' = [fork EXCEPT ![LeftF(self)] = N]
                             /\ pc' = [pc EXCEPT ![self] = "R"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "J0"]
                             /\ UNCHANGED << fork, state >>

R(self) == /\ pc[self] = "R"
           /\ fork' = [fork EXCEPT ![RightF(self)] = N]
           /\ pc' = [pc EXCEPT ![self] = "J0"]
           /\ state' = state

j(self) == J0(self) \/ HUNGRY(self) \/ P(self) \/ EATING(self)
              \/ EATING0(self) \/ THINKING(self) \/ R(self)

Next == (\E self \in Procs: j(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Mar 14 04:08:46 GMT 2022 by zunai
\* Created Mon Mar 14 02:41:51 GMT 2022 by zunai
