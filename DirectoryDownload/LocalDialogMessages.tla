---- MODULE LocalDialogMessages ------------------------------------------------
(* The messages Local can send to Dialog *)
--------------------------------------------------------------------------------
(* Request a dialog to be shown *)
RequestDialog ==
   [ message : {"request_dialog"} ]

MsgLocalToDialog ==
   UNION({
      RequestDialog
   })

================================================================================
