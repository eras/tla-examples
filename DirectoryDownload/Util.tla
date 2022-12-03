---- MODULE Util ---------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSetsExt

RECURSIVE SeqOfSet(_)
SeqOfSet(S) ==
   IF S # {}
   THEN LET element == CHOOSE x \in S: TRUE IN
        LET next_S == S \ {element} IN
        <<element>> \o SeqOfSet(next_S)
   ELSE <<>>

Image(F) == { F[x] : x \in DOMAIN F }

RECURSIVE SetOfSeqOf(_, _)
SetOfSeqOf(S, max_len) ==
  IF max_len > 0
  THEN {<<x>> \o tail: <<x, tail>> \in (S \X SetOfSeqOf(S, max_len - 1))} \cup SetOfSeqOf(S, max_len - 1)
  ELSE {<<>>}

RECURSIVE SetOfSeqWithLen(_, _)
SetOfSeqWithLen(S, len) ==
  IF len > 0
  THEN {<<x>> \o tail: <<x, tail>> \in (S \X SetOfSeqWithLen(S, len - 1))}
  ELSE {<<>>}

(* e.g. SetOfSeqWithDomain(LAMBDA id: Local(id)!InitSet, LocalIds)
   gives a set of functions from LocalIds to Local(id)!InitSets *)
RECURSIVE SetOfSeqWithDomain(_, _)
SetOfSeqWithDomain(S(_), domain) ==
  IF domain # {}
  THEN {Min(domain) :> x @@ tail: <<x, tail>> \in (S(Min(domain)) \X SetOfSeqWithDomain(S, domain \ {Min(domain)}))}
  ELSE {<<>>}

IndexWhere(P(_), seq) == CHOOSE index \in (1..Len(seq)): P(seq[index])

NoPrint(ignore, x) == x

Conforms(S, value) ==
  Assert(value \in S, <<"Value", value, "did not satisfy", S>>)

ConformsMsg(msg, S, value) ==
  Assert(value \in S, <<msg, "Value", value, "did not satisfy", S>>)

Check(S, value) ==
  IF Conforms(S, value)
  THEN value
  ELSE Assert(FALSE, "Impossible")

CheckMsg(msg, S, value) ==
  IF ConformsMsg(msg, S, value)
  THEN value
  ELSE Assert(FALSE, "Impossible")

NoCheck(S, value) ==
  value

QuieterCheck(S, value) ==
  IF Assert(value \in S, <<"Value", value, "did not satisfy criteria">>)
  THEN value
  ELSE Any

(*
PartsPerSize[1, 1] == << <<1>> >>
PartsPerSize[2, 1] == << <<1>>, <<2>> >>
PartsPerSize[3, 1] == << <<1>>, <<2>>>, <<3>> >>

PartsPerSize[1, 2] == << <<1, 2>> >>
PartsPerSize[2, 2] == << <<1, 2>>, <<3, 4>> >>
PartsPerSize[3, 2] == << <<1, 2>>, <<3, 4>>>, <<5, 6>> >>
*)
PartsPerSize(num_parts, size_per_part) ==
   LET size_range == Max(size_per_part) - Min(size_per_part) + 1 IN
   [x \in num_parts |-> {y + (x - Min(size_per_part)) * size_range: y \in size_per_part}]

================================================================================
