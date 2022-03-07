----------------------------- MODULE Telephone -----------------------------


=============================================================================
\* Modification History
\* Last modified Mon Mar 07 21:18:40 GMT+12:00 2022 by zunai
\* Created Mon Mar 06 21:17:31 GMT+12:00 2022 by zunaira
EXTENDS Sequences, TLC
(*--algorithm telephone
variables
  to_send = <<1, 2, 3>>,
  received = <<>>,
  in_transit = {};
begin
  while Len(received) /= 3 do
    \* send
    if in_send /= <<>> then
      in_transit := in_transit \union {Head(to_send)};
      to_send    := Tail(to_send);
    end if;
    \* receive
    either
      with msg \in in_transit do
        received   := Append(received, msg);
        in_transit := in_transit \ {msg};
      end with;
    or
      skip;
    end either;
  end while;
  assert recieved = <<1, 2, 3>>;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6642003a" /\ chksum(tla) = "6cf0d653")
VARIABLES to_send, received, in_transit, pc

vars == << to_send, received, in_transit, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) /= 3
               THEN /\ IF in_send /= <<>>
                          THEN /\ in_transit' = (in_transit \union {Head(to_send)})
                               /\ to_send' = Tail(to_send)
                          ELSE /\ TRUE
                               /\ UNCHANGED << to_send, in_transit >>
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ Assert(recieved = <<1, 2, 3>>, 
                              "Failure of assertion at line 31, column 3.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << to_send, in_transit >>
         /\ UNCHANGED received

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = Append(received, msg)
              /\ in_transit' = in_transit \ {msg}
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
