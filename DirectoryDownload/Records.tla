---- MODULE Records ------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE Naturals

CONSTANTS
   NumFiles
   , NumFileNames
   , MaxFileSize
   , MaxConcurrentTransfers

VARIABLES
   local_transfers

FileId == (1..NumFiles)
BlockId == (0..(MaxFileSize - 1))

TransferId == (1..MaxConcurrentTransfers)

\* Unused transfer slots are the empty tuple <<>>
FreeTransferId == {transfer_id \in TransferId: local_transfers[transfer_id] = <<>>}
ActiveTransferId == {transfer_id \in TransferId: local_transfers[transfer_id] # <<>>}

FileName == {"filename"} \X (1..NumFileNames)
FileSize == (0..MaxFileSize)

\* A file in the remote service is described by this
RemoteFile == [name: FileName,
               size: FileSize]

================================================================================
