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
   Receiver:   with n \in Node do
                    receive(ch[self], m);
                    if less(m.d + Edge[m.sendr, self], dist) then
                    dist := m.d + Edge[m.sendr, self];
                    parent := m.sendr;
                    else skip;
                    end if;
                 end with;
                 handle:   if self # m.sendr
                   then multicast(ch,[q \in neighbours(self) |-> [sendr |-> self, d |-> dist]]);
                   else skip;
                   end if;


end while;
end process;

end algorithm;*)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ceabaf812026ad9eb7fa274a2b6529a3
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
                  /\ \E n \in Node:
                       /\ \E _c1310 \in ch[self]:
                            /\ ch' = [ch EXCEPT ![self] = @ \ {_c1310}]
                            /\ m' = [m EXCEPT ![self] = _c1310]
                       /\ IF less(m'[self].d + Edge[m'[self].sendr, self], dist[self])
                             THEN /\ dist' = [dist EXCEPT ![self] = m'[self].d + Edge[m'[self].sendr, self]]
                                  /\ parent' = [parent EXCEPT ![self] = m'[self].sendr]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << dist, parent >>
                  /\ pc' = [pc EXCEPT ![self][1] = "handle"]
                  /\ UNCHANGED << msgs, ag >>

handle(self) == /\ pc[self][1]  = "handle"
                /\ IF self # m[self].sendr
                      THEN /\ ch' = [q \in DOMAIN ch |->  IF q \in neighbours ( self ) THEN ch[q] \cup  {[sendr|->self,d|->dist[self]]}  ELSE ch[q]]
                      ELSE /\ TRUE
                           /\ ch' = ch
                /\ pc' = [pc EXCEPT ![self][1] = "J0"]
                /\ UNCHANGED << msgs, ag, dist, parent, m >>

misra(self) == Sender(self) \/ J0(self) \/ Receiver(self) \/ handle(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node: misra(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : \A subprocess \in SubProcSet[self] : WF_vars(misra(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ec8631c2d4041892f11ddbd90ead7841

=============================================================================
\* Modification History
\* Last modified Thu Mar 24 04:26:17 GMT 2022 by zunai
\* Created Mon Mar 14 02:35:50 GMT 2022 by zunai
