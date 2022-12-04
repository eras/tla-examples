---- MODULE Util ---------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals

RECURSIVE SeqOfSet(_)
SeqOfSet(S) ==
   IF S # {}
   THEN LET element == CHOOSE x \in S: TRUE IN
        LET next_S == S \ {element} IN
        <<element>> \o SeqOfSet(next_S)
   ELSE <<>>

Image(F) == { F[x] : x \in DOMAIN F }

SeqRemoveIndex(S, Index) ==
   SubSeq(S, 1, Index - 1) \o SubSeq(S, Index + 1, Len(S))

================================================================================
