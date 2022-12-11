---- MODULE Dialog -------------------------------------------------------------
(* Implements a simple dialog that can be requested to open, and one that the
   user then can accept, after which the dialog is closed (and could be opened
   again) *)
--------------------------------------------------------------------------------
VARIABLES
   dialog_state                 (* state of the dialog *)
   , chan_local_to_dialog       (* channel to request dialog to be opened *)

vars == <<dialog_state, chan_local_to_dialog>>

LOCAL INSTANCE LocalDialogMessages
LOCAL INSTANCE DialogChannel

(* Used from Main to express this module does not modify variables *)
UnchangedVars == UNCHANGED vars

(* Startup state: dialog is closed *)
Init ==
   /\ dialog_state = "closed"
   (* chan_local_to_dialog initial value is set via Channels!Init *)

(* If a dialog is requested, open a dialog *)
Open(OtherUnchanged) ==
   /\ dialog_state = "closed"
   /\ LocalToDialog!Recv([ message |-> "request_dialog"])
   /\ dialog_state' = "open"
   /\ OtherUnchanged

(* Reset the dialog request and set it to accepted state if user acknowledges the dialog *)
Accept(OtherUnchanged) ==
   /\ dialog_state = "open"
   /\ dialog_state' = "accepted"
   /\ UNCHANGED<<chan_local_to_dialog>>
   /\ OtherUnchanged

(* Close accepted dialogs *)
Close(OtherUnchanged) ==
   /\ dialog_state = "accepted"
   /\ dialog_state' = "closed"
   /\ UNCHANGED<<chan_local_to_dialog>>
   /\ OtherUnchanged

(* A request to open the dialog; this is used by other modules, not by the Next action *)
Request ==
   /\ LocalToDialog!Send([ message |-> "request_dialog"])
   /\ UNCHANGED<<dialog_state>>

Next(OtherUnchanged) ==
   \/ Open(OtherUnchanged)
   \/ Accept(OtherUnchanged)
   \/ Close(OtherUnchanged)

(* Quiescent: none of the Next actions can be taken *)
Quiescent == ~ENABLED Next(TRUE)

(* For tlsd *)
State ==
  [ state |-> dialog_state ]

================================================================================
