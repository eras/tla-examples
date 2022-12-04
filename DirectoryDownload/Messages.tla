---- MODULE Messages -----------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------

CONSTANTS
   NumFiles                 \* Needed for Records
   , MaxFileSize            \* Needed for Records
   , MaxConcurrentTransfers \* Needed for Records

LOCAL INSTANCE Records

RequestListFiles ==
  [ message: {"list_files"} ]

RespondListFiles ==
   UNION({
      [ message : {"list_files"},
        file    : RemoteFile ],
      [ message : {"end_list_files"} ]
   })

RequestFileBlock ==
   [ message: {"file_block"},
     name   : FileName,
     block  : BlockId ]

RespondFileBlock ==
   [ message: {"file_block"},
     name   : FileName,
     block  : BlockId ]

MsgLocalToRemote ==
  UNION({
     RequestListFiles,
     RequestFileBlock
  })

MsgRemoteToLocal ==
   UNION({
      RespondListFiles,
      RespondFileBlock
   })

================================================================================
