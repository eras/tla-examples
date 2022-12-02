---- MODULE FileTransfer -------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE TLC

CONSTANTS
   NumFiles
   , NumFileNames
   , MaxFileSize
   , MaxConcurrentTransfers

VARIABLES
   peer_files                   (* The files the peer has *)
   , local_files                (* The files the client knows of *)
   , scanner_state              (* State of the scanner *)
   , transfers                  (* On-going transfers *)

vars == <<peer_files, local_files, scanner_state, transfers>>

FileId == (1..NumFiles)

TransferId == (1..MaxConcurrentTransfers)

\* Unused transfer slots are the empty tuple <<>>
FreeTransferId == {transfer_id \in TransferId: transfers[transfer_id] = <<>>}
ActiveTransferId == {transfer_id \in TransferId: transfers[transfer_id] # <<>>}

FileName == {"filename"} \X (1..NumFileNames)
FileSize == (0..MaxFileSize)

\* A file in the remote service is described by this
PeerFile == [name: FileName,
             size: FileSize]

\* Local information about the remote files
LocalFile == [peer_file   : PeerFile,
              transfer_id : {0} \cup TransferId,
              state       : {"ignore", "waiting-transfer", "transferring", "transferred"}]

\* An on-going transfer of a file
Transfer == [peer_file  : PeerFile,
             state      : {"active", "transfer", "finished"},
             local_size : FileSize,
             file_id    : FileId]

----
\* TypeOK invariants
PeerFileTypeOK     ==
  /\ \A peer_file \in peer_files: peer_file \in PeerFile
  /\ ~ \E peer_file1 \in peer_files:
     \E peer_file2 \in peer_files:
     /\ peer_file1.name = peer_file2.name
     /\ peer_file1.size # peer_file2.size
LocalFileTypeOK    == local_files \in [FileId -> {<<>>} \cup LocalFile]
ScannerStateTypeOK == scanner_state \in {"idle", "scanning", "scanned"}
TransfersTypeOK    == transfers \in [TransferId -> {<<>>} \cup Transfer]

TypeOK ==
  /\ PeerFileTypeOK
  /\ LocalFileTypeOK
  /\ ScannerStateTypeOK
  /\ TransfersTypeOK

----
\* Generate uniquely named file of different names and varying sizes
RECURSIVE GenerateFiles(_)
GenerateFiles(files) ==
  IF \E file \in PeerFile: file.name \notin {file2.name: file2 \in files}
  THEN LET file == CHOOSE file \in PeerFile:
                   /\ file.name \notin {file2.name: file2 \in files}
                   /\ \lnot \E file2 \in files: file.size <= file2.size
       IN GenerateFiles({file} \union files)
  ELSE files

\* Set of files we are locally aware of
HasFileId == {file_id \in FileId: local_files[file_id] # <<>>}

\* Set of file names we are locally aware of
LocalFileNames == {local_files[file_id].peer_file.name: file_id \in HasFileId}

\* Are we locally aware of this file in the peer?
FoundLocally(peer_file) == \E local_file_name \in LocalFileNames: peer_file.name = local_file_name

----
(* Scanning *)

(* If scanner is idle, start scanning *)
ScanStart ==
  /\ scanner_state = "idle"
  /\ scanner_state' = "scanning"
  /\ UNCHANGED<<transfers, peer_files, local_files>>

(* If scanner is scanning, find a file we're not locally aware of and copy its information *)
(* If no such files are found, finish scanning *)
ScanDo ==
  /\ scanner_state = "scanning"
  /\ IF \E peer_file \in peer_files: ~FoundLocally(peer_file) THEN
        LET peer_file == CHOOSE peer_file \in peer_files: ~FoundLocally(peer_file) IN
        LET file_id == CHOOSE file_id \in FileId: local_files[file_id] = <<>> IN
        /\ local_files' = [local_files EXCEPT ![file_id] = [peer_file |-> peer_file,
                                                            transfer_id |-> 0,
                                                            state |-> "waiting-transfer"]]
        /\ UNCHANGED<<transfers, peer_files, scanner_state>>
     ELSE
        /\ scanner_state' = "scanned"
        /\ UNCHANGED<<transfers, peer_files, local_files>>

(* Transfer *)

(* Are there free slots in the transfers structure? *)
HasFreeTransferSlot == \E transfer_id \in TransferId: transfers[transfer_id] = <<>>

(* Are there files that are waiting for transfer? *)
HasFileWaitingTransfer == \E file_id \in HasFileId: local_files[file_id].state = "waiting-transfer"

(* If the scanner has scanned, there are free transfer slots and there are files waiting transfer,
 * pick one such file and start the transfer. *)
TransferStart ==
  /\ scanner_state = "scanned"
  /\ HasFreeTransferSlot /\ HasFileWaitingTransfer
  /\ \E file_id \in HasFileId: local_files[file_id].state = "waiting-transfer"
  /\ \E transfer_id \in FreeTransferId:
     LET file_id == CHOOSE file_id \in HasFileId: local_files[file_id].state = "waiting-transfer" IN
     LET local_file == local_files[file_id] IN
     /\ transfers' = [transfers EXCEPT ![transfer_id] = [peer_file  |-> local_file.peer_file,
                                                         state      |-> "active",
                                                         local_size |-> 0,
                                                         file_id    |-> file_id]]
     /\ local_files' = [local_files EXCEPT ![file_id] = [@ EXCEPT !.transfer_id     = transfer_id,
                                                                  !.state           = "transferring"]]
     /\ UNCHANGED<<peer_files, scanner_state>>

(* If there are active transfers, transfer one unit of data. If the file has already transferred
 * all the data, mark it finished.  *)
TransferDo ==
  \E transfer_id \in ActiveTransferId:
  LET transfer == transfers[transfer_id] IN
  /\ transfer.state = "active"
  /\ IF transfer.local_size < transfer.peer_file.size
     THEN transfers' = [transfers EXCEPT ![transfer_id] = [@ EXCEPT !.local_size = transfer.local_size + 1]]
     ELSE transfers' = [transfers EXCEPT ![transfer_id] = [@ EXCEPT !.state = "finished"]]
  /\ UNCHANGED<<peer_files, local_files, scanner_state>>

(* If the transfer is finished, release the transfer slot and mark the local file transferred *)
TransferFinished ==
  \E transfer_id \in ActiveTransferId:
  LET transfer == transfers[transfer_id] IN
  LET file_id == transfer.file_id IN
  /\ transfer.state = "finished"
  /\ transfers' = [transfers EXCEPT ![transfer_id] = <<>>]
  /\ local_files' = [local_files EXCEPT ![file_id] = [@ EXCEPT !.transfer_id     = 0,
                                                               !.state           = "transferred"]]
  /\ UNCHANGED<<peer_files, scanner_state>>

----
(* State *)

Stutter == UNCHANGED<<vars>>

Next ==
  \/ ScanStart
  \/ ScanDo
  \/ TransferStart
  \/ TransferDo
  \/ TransferFinished
\*  \/ Stutter

Init ==
  /\ peer_files    = GenerateFiles({})
  /\ local_files   = [file_id \in FileId |-> <<>>]
  /\ transfers     = [transfer_id \in TransferId |-> <<>>]
  /\ scanner_state = "idle"

(* Properties *)

EventuallyAllFilesAreTransferred ==
  Init =>
  <>\A peer_file \in peer_files:
    \E file_id \in HasFileId:
    /\ local_files[file_id].peer_file = peer_file
    /\ local_files[file_id].state = "transferred"

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

================================================================================
