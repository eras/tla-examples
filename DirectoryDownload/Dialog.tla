---- MODULE Dialog -------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
VARIABLES
   dialog_state                 (* state of the dialog *)
   , dialog_request             (* is there a request to open the dialog? *)

vars == <<dialog_state, dialog_request>>

(* Used from Main to express this module does not modify variables *)
UnchangedVars == UNCHANGED vars

(* Startup state: dialog is closed *)
Init ==
   /\ dialog_state = "closed"
   /\ dialog_request = FALSE

(* If a dialog is requested, open a dialog *)
Open ==
   /\ dialog_state = "closed"
   /\ dialog_request = TRUE
   /\ dialog_state' = "open"
   /\ UNCHANGED<<dialog_request>>

(* Reset the dialog request and set it to accepted state if user acknowledges the dialog *)
Accept ==
   /\ dialog_state = "open"
   /\ dialog_request' = FALSE
   /\ dialog_state' = "accepted"

(* Close accepted dialogs *)
Close ==
   /\ dialog_state = "accepted"
   /\ dialog_state' = "closed"
   /\ UNCHANGED<<dialog_request>>

(* A request to open the dialog; this is used by other modules, not by the Next action *)
Request ==
   /\ dialog_request' = TRUE
   /\ UNCHANGED<<dialog_state>>

Next ==
   \/ Open
   \/ Accept
   \/ Close

(* Quiescent: none of the Next actions can be taken *)
Quiescent == ~ENABLED Next

================================================================================
