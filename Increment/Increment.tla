---- MODULE Increment ----------------------------------------------------------
EXTENDS Naturals, TLC
CONSTANTS N, P

(* --algorithm IncrementAlg

variables u = 1 ;

process Proc \in 1..P
begin
  comp : while u < N do
  incr :   u := u + 1;
           assert u <= N;
         end while;
end process

end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "b1cfbdb9" /\ chksum(tla) = "a30cbb63")
VARIABLES u, pc

vars == << u, pc >>

ProcSet == (1..P)

Init == (* Global variables *)
        /\ u = 1
        /\ pc = [self \in ProcSet |-> "comp"]

comp(self) == /\ pc[self] = "comp"
              /\ IF u < N
                    THEN /\ pc' = [pc EXCEPT ![self] = "incr"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ u' = u

incr(self) == /\ pc[self] = "incr"
              /\ u' = u + 1
              /\ Assert(u' <= N, 
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
