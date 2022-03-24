-------------------------- MODULE chandymisraalgo --------------------------
EXTENDS TLC, Naturals, Integers, Sequences
CONSTANTS Node, Edge, Initiator
infnty == CHOOSE i: i \notin Nat
noNode == CHOOSE i: i \notin Node
ASSUME Edge \in [Node \X Node -> Nat] \*Edge == weights of edges

(* PlusCal options (-distpcal) *)

(*--algorithm chandy
\*Consider msgs as parentP in algo
variables msgs = [n \in Node |-> {}];
channels ch[Node], ag[Node];
define
less(d, e) == IF d=infnty THEN FALSE
              ELSE IF e = infnty THEN TRUE
              ELSE d<e
neighbours(a) == {n \in Node: n#a /\ Edge[a, n]>0}
neighbreseiver(a,s) == {n \in Node: n#s /\ n#a /\ Edge[a, n]>0}
end define;
fair process misra \in Node
     variables dist = IF self = Initiator THEN 0 ELSE infnty,
               parent = noNode, m;
     begin
     Sender: if self = Initiator then
               multicast(ch,[n \in neighbours(self) |-> [sendr |-> self, d |-> 0]]);
               else skip;
             end if;

     J0: while TRUE do

     Receiver:   receive(ch[self], m);
                 if less(m.d + Edge[m.sendr, self], dist) then
                    dist := m.d + Edge[m.sendr, self];
                    parent := m.sendr;
                     multicast(ch,[n \in neighbours(self) |-> [sendr |-> self, d |-> dist]]);
                     \*    broadcast(ch, [n \in neighbreseiver(m.sendr,self) |-> [sendr |-> self, d |-> dist]]);
                  else skip;
                  end if;

end while;
end process;

end algorithm;*)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-abee463d12ccb87eb9ede1fb831fb703
CONSTANT defaultInitValue
VARIABLES msgs, ch, ag, pc

(* define statement *)
less(d, e) == IF d=infnty THEN FALSE
              ELSE IF e = infnty THEN TRUE
              ELSE d<e
neighbours(a) == {n \in Node: n#a /\ Edge[a, n]>0}
neighbreseiver(a,s) == {n \in Node: n#s /\ n#a /\ Edge[a, n]>0}

VARIABLES dist, parent, m

vars == << msgs, ch, ag, pc, dist, parent, m >>

ProcSet == (Node)

SubProcSet == [_n1 \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ msgs = [n \in Node |-> {}]
        /\ ch = [_n20 \in Node |-> {}]
        /\ ag = [_n30 \in Node |-> {}]
        (* Process misra *)
        /\ dist = [self \in Node |-> IF self = Initiator THEN 0 ELSE infnty]
        /\ parent = [self \in Node |-> noNode]
        /\ m = [self \in Node |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> <<"Sender">>]

Sender(self) == /\ pc[self][1]  = "Sender"
                /\ IF self = Initiator
                      THEN /\ ch' = [n \in DOMAIN ch |->  IF n \in neighbours ( self ) THEN ch[n] \cup  {[sendr|->self,d|->0]}  ELSE ch[n]]
                      ELSE /\ TRUE
                           /\ ch' = ch
                /\ pc' = [pc EXCEPT ![self][1] = "J0"]
                /\ UNCHANGED << msgs, ag, dist, parent, m >>

J0(self) == /\ pc[self][1]  = "J0"
            /\ pc' = [pc EXCEPT ![self][1] = "Receiver"]
            /\ UNCHANGED << msgs, ch, ag, dist, parent, m >>

Receiver(self) == /\ pc[self][1]  = "Receiver"
                  /\ \E _c1310 \in ch[self]:
                       /\ ch' = [ch EXCEPT ![self] = @ \ {_c1310}]
                       /\ m' = [m EXCEPT ![self] = _c1310]
                  /\ IF less(m'[self].d + Edge[m'[self].sendr, self], dist[self])
                        THEN /\ dist' = [dist EXCEPT ![self] = m'[self].d + Edge[m'[self].sendr, self]]
                             /\ parent' = [parent EXCEPT ![self] = m'[self].sendr]
                             /\ pc' = [pc EXCEPT ![self][1] = "Lbl_1"]
                        ELSE /\ TRUE
                             /\ pc' = [pc EXCEPT ![self][1] = "J0"]
                             /\ UNCHANGED << dist, parent >>
                  /\ UNCHANGED << msgs, ag >>

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ ch' = [n \in DOMAIN ch |->  IF n \in neighbours ( self ) THEN ch[n] \cup  {[sendr|->self,d|->dist[self]]}  ELSE ch[n]]
               /\ pc' = [pc EXCEPT ![self][1] = "J0"]
               /\ UNCHANGED << msgs, ag, dist, parent, m >>

misra(self) == Sender(self) \/ J0(self) \/ Receiver(self) \/ Lbl_1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node: misra(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : \A subprocess \in SubProcSet[self] : WF_vars(misra(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-0a450c4011ca4c9dd2549508ae376ac5

=============================================================================
\* Modification History
\* Last modified Thu Mar 24 03:10:50 GMT 2022 by zunai
\* Created Mon Mar 14 02:35:50 GMT 2022 by zunai
