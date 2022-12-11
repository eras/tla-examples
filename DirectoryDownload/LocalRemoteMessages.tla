---- MODULE LocalRemoteMessages ------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------

CONSTANTS
   NumFiles                 \* Needed for LocalRemoteTypes
   , MaxFileSize            \* Needed for LocalRemoteTypes
   , MaxConcurrentTransfers \* Needed for LocalRemoteTypes

LOCAL INSTANCE LocalRemoteTypes

(* Request a list of files from the remote *)
RequestListFiles ==
  [ message: {"list_files"} ]

(* Respond with one file, or the indication of the end of list *)
RespondListFiles ==
   UNION({
      [ message : {"list_files"},
        file    : RemoteFile ],
      [ message : {"end_list_files"} ]
   })

(* Request one block of a named file *)
RequestFileBlock ==
   [ message: {"file_block"},
     name   : FileName,
     block  : BlockId ]

(* Respond one block of a named file *)
RespondFileBlock ==
   [ message: {"file_block"},
     name   : FileName,
     block  : BlockId ]

(* All messages from local to remote *)
MsgLocalToRemote ==
  UNION({
     RequestListFiles,
     RequestFileBlock
  })

(* All messages from remote to local *)
MsgRemoteToLocal ==
   UNION({
      RespondListFiles,
      RespondFileBlock
   })

================================================================================
