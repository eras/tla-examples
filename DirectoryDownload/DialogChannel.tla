---- MODULE DialogChannel ------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
VARIABLES
   chan_local_to_dialog         (* Channel from local to dialog *)

LOCAL INSTANCE LocalDialogMessages

LocalToDialog == INSTANCE Channel WITH channel <- chan_local_to_dialog, Data <- MsgLocalToDialog

================================================================================
