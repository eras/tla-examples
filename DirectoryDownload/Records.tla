---- MODULE Records ------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE Naturals

CONSTANTS
   NumFiles
   , NumFileNames
   , MaxFileSize
   , MaxConcurrentTransfers

FileId == (1..NumFiles)
BlockId == (0..(MaxFileSize - 1))

TransferId == (1..MaxConcurrentTransfers)

FileName == {"filename"} \X (1..NumFileNames)
FileSize == (0..MaxFileSize)

\* A file in the remote service is described by this
RemoteFile == [name: FileName,
               size: FileSize]

================================================================================
