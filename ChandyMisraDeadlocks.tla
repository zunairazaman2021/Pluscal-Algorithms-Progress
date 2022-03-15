------------------------ MODULE ChandyMisraDeadlocks ------------------------
EXTENDS TLC, Naturals, Integers, Sequences
CONSTANTS Node, Edge, Initiator
infnty == CHOOSE i: i \notin Nat
noNode == CHOOSE i: i \notin Node 
ASSUME Edge \in [Node \X Node -> Nat] \*Edge == weights of edges
(*--algorithm chandy
\*Consider msgs as parentP in algo
variables msgs = [n \in Node |-> {}];
define
less(d, e) == IF d=infnty THEN FALSE
              ELSE IF e = infnty THEN TRUE 
              ELSE d<e
end define;

fair process misra \in Node
     variables dist = IF self = Initiator THEN 0 ELSE infnty,
               parent = noNode;
     begin

     Sender: if self = Initiator then 
                  msgs := [n \in Node |-> 
                           IF n # self /\ Edge[self, n] > 0
                           THEN msgs[n] \union {[sendr |-> self, d |-> 0]}
                           ELSE msgs[n]]
              end if;
      J0:     while TRUE do
      Reciever: with m \in msgs[self] do
                     if less(m.d + Edge[m.sendr, self] , dist) then
                            dist :=  m.d + Edge[m.sendr, self];
                            parent := m.sendr;
                            msgs := [n \in Node |-> 
                                     IF n # m.sendr /\ n # self /\ Edge[self, n] > 0
                                     THEN msgs[n] \union {[sendr |-> self, d |-> dist]}
                                     ELSE IF n = self THEN msgs[n] \ {m}
                                     ELSE msgs[n]]
                       else 
                           msgs[self] := msgs[self] \ {m}              
                      end if;
               end with;    
     end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "efc674da" /\ chksum(tla) = "ea341011")
VARIABLES msgs, pc

(* define statement *)
less(d, e) == IF d=infnty THEN FALSE
              ELSE IF e = infnty THEN TRUE
              ELSE d<e

VARIABLES dist, parent

vars == << msgs, pc, dist, parent >>

ProcSet == (Node)

Init == (* Global variables *)
        /\ msgs = [n \in Node |-> {}]
        (* Process misra *)
        /\ dist = [self \in Node |-> IF self = Initiator THEN 0 ELSE infnty]
        /\ parent = [self \in Node |-> noNode]
        /\ pc = [self \in ProcSet |-> "Sender"]

Sender(self) == /\ pc[self] = "Sender"
                /\ IF self = Initiator
                      THEN /\ msgs' = [n \in Node |->
                                       IF n # self /\ Edge[self, n] > 0
                                       THEN msgs[n] \union {[sendr |-> self, d |-> 0]}
                                       ELSE msgs[n]]
                      ELSE /\ TRUE
                           /\ msgs' = msgs
                /\ pc' = [pc EXCEPT ![self] = "J0"]
                /\ UNCHANGED << dist, parent >>

J0(self) == /\ pc[self] = "J0"
            /\ pc' = [pc EXCEPT ![self] = "Reciever"]
            /\ UNCHANGED << msgs, dist, parent >>

Reciever(self) == /\ pc[self] = "Reciever"
                  /\ \E m \in msgs[self]:
                       IF less(m.d + Edge[m.sendr, self] , dist[self])
                          THEN /\ dist' = [dist EXCEPT ![self] = m.d + Edge[m.sendr, self]]
                               /\ parent' = [parent EXCEPT ![self] = m.sendr]
                               /\ msgs' = [n \in Node |->
                                           IF n # m.sendr /\ n # self /\ Edge[self, n] > 0
                                           THEN msgs[n] \union {[sendr |-> self, d |-> dist'[self]]}
                                           ELSE IF n = self THEN msgs[n] \ {m}
                                           ELSE msgs[n]]
                          ELSE /\ msgs' = [msgs EXCEPT ![self] = msgs[self] \ {m}]
                               /\ UNCHANGED << dist, parent >>
                  /\ pc' = [pc EXCEPT ![self] = "J0"]

misra(self) == Sender(self) \/ J0(self) \/ Reciever(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node: misra(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(misra(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Mon Mar 14 17:02:21 GMT 2022 by zunai
\* Created Mon Mar 14 10:46:43 GMT 2022 by zunai
