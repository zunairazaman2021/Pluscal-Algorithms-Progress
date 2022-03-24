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
channels ch[Node];
define
less(d, e) == IF d=infnty THEN FALSE
              ELSE IF e = infnty THEN TRUE
              ELSE d<e
neighbours(a) == {n \in Node: n#a /\ Edge[a, n]}
neighbreseiver(a,s) == {n \in Node: n#s /\ n#a /\ Edge[a, n]}
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
                  with n \in Node do
                        if n#m.sendr /\ n#self /\ Edge[self, n] > 0
                        then send(ch[self],  [sendr |-> self, d |-> dist]);
                        else skip;
                        end if;
                    end with;
                 end if;
end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4f9a6e75368b4d87499eb21a659e70af
CONSTANT defaultInitValue
VARIABLES msgs, ch, pc

(* define statement *)
less(d, e) == IF d=infnty THEN FALSE
              ELSE IF e = infnty THEN TRUE
              ELSE d<e
neighbours(a) == {n \in Node: n#a /\ Edge[a, n]}
neighbreseiver(a,s) == {n \in Node: n#s /\ n#a /\ Edge[a, n]}

VARIABLES dist, parent, m

vars == << msgs, ch, pc, dist, parent, m >>

ProcSet == (Node)

SubProcSet == [_n1 \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ msgs = [n \in Node |-> {}]
        /\ ch = [_n20 \in Node |-> {}]
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
                /\ UNCHANGED << msgs, dist, parent, m >>

J0(self) == /\ pc[self][1]  = "J0"
            /\ pc' = [pc EXCEPT ![self][1] = "Receiver"]
            /\ UNCHANGED << msgs, ch, dist, parent, m >>

Receiver(self) == /\ pc[self][1]  = "Receiver"
                  /\ \E _c1310 \in ch[self]:
                       /\ ch' = [ch EXCEPT ![self] = @ \ {_c1310}]
                       /\ m' = [m EXCEPT ![self] = _c1310]
                  /\ IF less(m'[self].d + Edge[m'[self].sendr, self], dist[self])
                        THEN /\ dist' = [dist EXCEPT ![self] = m'[self].d + Edge[m'[self].sendr, self]]
                             /\ parent' = [parent EXCEPT ![self] = m'[self].sendr]
                             /\ pc' = [pc EXCEPT ![self][1] = "Lbl_1"]
                        ELSE /\ pc' = [pc EXCEPT ![self][1] = "J0"]
                             /\ UNCHANGED << dist, parent >>
                  /\ msgs' = msgs

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ \E n \in Node:
                    IF n#m[self].sendr /\ n#self /\ Edge[self, n] > 0
                       THEN /\ ch' = [ch EXCEPT ![self] = @ \cup {[sendr |-> self, d |-> dist[self]]}]
                       ELSE /\ TRUE
                            /\ ch' = ch
               /\ pc' = [pc EXCEPT ![self][1] = "J0"]
               /\ UNCHANGED << msgs, dist, parent, m >>

misra(self) == Sender(self) \/ J0(self) \/ Receiver(self) \/ Lbl_1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node: misra(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : \A subprocess \in SubProcSet[self] : WF_vars(misra(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-719c97364fceb2a26ca36a3a91f08f0d

=============================================================================
\* Modification History
\* Last modified Tue Mar 22 10:30:58 GMT 2022 by zunai
\* Created Mon Mar 14 02:35:50 GMT 2022 by zunai
