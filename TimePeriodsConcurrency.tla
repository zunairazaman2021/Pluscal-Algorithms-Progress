----------------------- MODULE TimePeriodsConcurrency -----------------------
EXTENDS Integers
CONSTANTS ResourceCap, MaxConsumerReq, Actors

ASSUME ResourceCap > 0
ASSUME Actors /={}
ASSUME MaxConsumerReq \in 1..ResourceCap

(*--algorithm cache
variables res_left = ResourceCap;

define 
     ResourceInvariant == res_left >= 0
end define;

process time = "time"
    begin 
         Tick:
            res_left := ResourceCap;
            goto Tick;
end process;

process actor \in Actors
    variables res_needed \in 1..MaxConsumerReq
    begin
         UseResources: 
              while TRUE do 
              await res_left >= res_needed;
              res_left := res_left - res_needed; 
              end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "e3cb8206" /\ chksum(tla) = "4c8e46")
VARIABLES res_left, pc

(* define statement *)
ResourceInvariant == res_left >= 0

VARIABLE res_needed

vars == << res_left, pc, res_needed >>

ProcSet == {"time"} \cup (Actors)

Init == (* Global variables *)
        /\ res_left = ResourceCap
        (* Process actor *)
        /\ res_needed \in [Actors -> 1..MaxConsumerReq]
        /\ pc = [self \in ProcSet |-> CASE self = "time" -> "Tick"
                                        [] self \in Actors -> "UseResources"]

Tick == /\ pc["time"] = "Tick"
        /\ res_left' = ResourceCap
        /\ pc' = [pc EXCEPT !["time"] = "Tick"]
        /\ UNCHANGED res_needed

time == Tick

UseResources(self) == /\ pc[self] = "UseResources"
                      /\ res_left >= res_needed[self]
                      /\ res_left' = res_left - res_needed[self]
                      /\ pc' = [pc EXCEPT ![self] = "UseResources"]
                      /\ UNCHANGED res_needed

actor(self) == UseResources(self)

Next == time
           \/ (\E self \in Actors: actor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Mar 08 23:52:15 GMT+12:00 2022 by zunai
\* Created Tue Mar 08 22:00:52 GMT+12:00 2022 by zunai
