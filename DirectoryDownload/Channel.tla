------------------------------ MODULE Channel -------------------------------

(* Channel is an asynchronous channel between with a buffer of at most
   one message.

   The state is stored in the channel function. Channels maps via Id to the
   actual channel.

   Copyright 2022 Erkki Seppälä <erkki.seppala@vincit.fi>
*)

----------------------------------------------------------------------------
LOCAL INSTANCE TLC              (* Assert *)

CONSTANT Data                   (* Data constrains the kind of messages this module processes*)

VARIABLE channel                (* Channel *)

UnchangedVars == UNCHANGED channel

(* When a channel is not busy, it has this value. Redundant really to
   have the 'busy' flag at all, but maybe it makes things more clear
*)
Null == <<>>

ASSUME Null \notin Data

Channel == [val: Data \cup {Null}, busy: BOOLEAN]

TypeOK == channel \in Channel

Send(data) ==
   /\ Assert(data \in Data, <<"Sending invalid data", data, "while expecting", Data>>)
   /\ \lnot channel.busy
   /\ channel' = [val |-> data, busy |-> TRUE]

Recv(data) ==
   /\ Assert(data \in Data, <<"Receiving invalid data", data, "while expecting", Data>>)
   /\ channel.busy
   /\ data = channel.val
   /\ channel' = [val |-> Null, busy |-> FALSE]

Sending ==
   IF channel.busy
   THEN {channel.val}
   ELSE {}

Init ==
   channel = [val |-> Null, busy |-> FALSE]

=============================================================================
