---- MODULE LocalDialogMessages ------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
(* Request a dialog to be shown *)
RequestDialog ==
   [ message : {"request_dialog"} ]

MsgLocalToDialog ==
   UNION({
      RequestDialog
   })

================================================================================
