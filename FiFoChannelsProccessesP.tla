---------------------- MODULE FiFoChannelsProccessesP ----------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

variable cur = "none";
fifo f_chan[Nodes];

process w \in Nodes
begin
    Write:
    while ( TRUE ) do
            send(f_chan[self], "msg");
    end while;
end process;

process r \in Nodes
begin
    Read:
    while ( TRUE ) do
            receive(f_chan[self], cur);
    end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "93acdfa4" /\ chksum(tla) = "dfc735b2")
VARIABLES cur, f_chan, pc

vars == << cur, f_chan, pc >>

ProcSet == (Nodes) \cup (Nodes)

Genprocs1 == { <<p>>: p \in Nodes }

Genprocs2 == { <<p>>: p \in Nodes }

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in Nodes THEN 1..1
                                 ELSE (**Nodes**) 1..1]

Init == (* Global variables *)
        /\ cur = "none"
        /\ f_chan = [_n20 \in Nodes |-> <<>>]
        /\ pc = [self \in Genprocs1 \union Genprocs2 |-> CASE  self \in Genprocs1 -> "Write"
		 [] self \in Genprocs2 -> "Read" ]

Write(self) == /\ pc[<<self >>] = "Write"
               /\ f_chan' = [f_chan EXCEPT ![self] =  Append(@, "msg")]
               /\ pc' = [pc EXCEPT ![<<self>>] = "Write"]
               /\ cur' = cur

w(self) == Write(self)


Read(self) == /\ pc[<<self >>] = "Read"
              /\ Len(f_chan[self]) > 0 
              /\ cur' = Head(f_chan[self])
              /\ f_chan' = [f_chan EXCEPT ![self] =  Tail(@) ]
              /\ pc' = [pc EXCEPT ![<<self>>] = "Read"]

r(self) == Read(self)


Next ==    \/ (\E self \in Nodes: w(self))
           \/ (\E self \in Nodes: r(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Jun 24 10:20:16 GMT 2022 by zunai
\* Created Fri Jun 24 10:20:11 GMT 2022 by zunai
