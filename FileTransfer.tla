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
   peer_files
   , local_files
   , scanner_state

vars == <<peer_files, local_files, scanner_state>>

FileId == (1..NumFiles)

FileName == {"filename"} \X (1..NumFileNames)

PeerFile == [name: FileName,
             size: (0..MaxFileSize)]

LocalFile == {<<>>} \cup [peer_file: PeerFile]

RECURSIVE GenerateFiles(_)
GenerateFiles(files) ==
  IF \E file \in PeerFile: file.name \notin {file2.name: file2 \in files}
  THEN LET file == CHOOSE file \in PeerFile:
                   /\ file.name \notin {file2.name: file2 \in files}
                   /\ \lnot \E file2 \in files: file.size <= file2.size
       IN GenerateFiles({file} \union files)
  ELSE files

HasFileId == {file_id \in FileId: local_files[file_id] # <<>>}

LocalFileNames == {local_files[file_id].peer_file.name: file_id \in HasFileId}

NotFoundLocally(peer_file) == \lnot \E local_file_name \in LocalFileNames: peer_file.name = local_file_name

(* scanning *)

Scan1 ==
  /\ scanner_state = "idle"
  /\ scanner_state' = "scanning"
  /\ UNCHANGED<<peer_files, local_files>>

Scan2 ==
  IF \E peer_file \in peer_files: NotFoundLocally(peer_file) THEN
     LET peer_file == CHOOSE peer_file \in peer_files: NotFoundLocally(peer_file) IN
     LET file_id == CHOOSE file_id \in FileId: local_files[file_id] = <<>> IN
     /\ local_files' = [local_files EXCEPT ![file_id] = [peer_file |-> peer_file]]
     /\ UNCHANGED<<peer_files, scanner_state>>
  ELSE
     /\ scanner_state' = "scanned"
     /\ UNCHANGED<<peer_files, local_files>>

(* Next state *)

Stutter ==
  /\ UNCHANGED<<vars>>

Next ==
  \/ Scan1
  \/ Scan2
  \/ Stutter

Init ==
  /\ peer_files = GenerateFiles({})
  /\ local_files = [file_id \in FileId |-> <<>>]
  /\ scanner_state = "idle"

Spec ==
  /\ Init
  /\ [][Next]_vars
  (* /\ []WF_vars(Next) *)

================================================================================
