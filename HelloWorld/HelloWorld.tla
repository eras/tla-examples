---- MODULE HelloWorld ---------------------------------------------------------
(* Documentation *)

VARIABLES words

vars == <<words>>

AllWords == {"Hello", "Shitty", "World"}

TypeOK ==
  /\ words \in SUBSET AllWords

Init ==
  /\ words = {}

RemoveWord ==
  /\ \E word \in words: words' = words \ {word}

AddWord ==
  /\ \E word \in AllWords: /\ word \notin words
                           /\ words' = words \cup {word}

Next ==
  \/ RemoveWord
  \/ AddWord

Spec ==
  /\ Init
  /\ [][Next]_vars

--------------------------------------------------------------------------------

HelloConstraint == {"Hello", "World"} # words

================================================================================
