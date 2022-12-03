---- MODULE Increment ----------------------------------------------------------
EXTENDS Naturals, TLC
CONSTANTS N, P

(* --algorithm IncrementAlg

variables n = 1;

process Proc \in 1..P
begin
  comp : while n < N do
  incr :   n := n + 1;
           assert n <= N;
         end while;
end process

end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "a6f1d42c" /\ chksum(tla) = "fc6522d9")
VARIABLES n, pc

vars == << n, pc >>

ProcSet == (1..P)

Init == (* Global variables *)
        /\ n = 1
        /\ pc = [self \in ProcSet |-> "comp"]

comp(self) == /\ pc[self] = "comp"
              /\ IF n < N
                    THEN /\ pc' = [pc EXCEPT ![self] = "incr"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ n' = n

incr(self) == /\ pc[self] = "incr"
              /\ n' = n + 1
              /\ Assert(n' <= N, 
                        "Failure of assertion at line 13, column 12.")
              /\ pc' = [pc EXCEPT ![self] = "comp"]

Proc(self) == comp(self) \/ incr(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..P: Proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

--------------------------------------------------------------------------------

================================================================================
