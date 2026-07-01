---- MODULE spec ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

\* https://ubuntu.com/blog/hunting-a-16-year-old-sqlite-bug-with-tla-is-dqlite-affected
VARIABLES wal,
          db,
          nBackfill,
          mxFrame,
          walSalt,
          writeLock,
          checkpointState,
          pWalSalt,
          safeMxFrame,
          frameNumber

checkpoint_vars == <<>>

Init ==
  /\ wal = <<>>
  /\ db = {}
  /\ nBackfill = 0
  /\ mxFrame = 0
  /\ walSalt = 0

WalAppendTakeLock ==
  /\ writeLock = "notTaken"
  /\ writeLock' = "takenForAppend"
  /\ UNCHANGED << wal,
        db,
        nBackfill,
        mxFrame,
        frameNumber,
        checkpointState,
        safeMxFrame,
        walSalt,
        pWalSalt
     >>

WalAppend ==
  /\ writeLock = "takenForAppend"
  /\ IF nBackfill > 0 /\ mxFrame = nBackfill
     THEN /\ wal' = << frameNumber >>
          /\ mxFrame' = 1
          /\ nBackfill' = 0
          /\ walSalt' = walSalt + 1
     ELSE /\ wal' = Append(wal, frameNumber)
          /\ mxFrame' = mxFrame + 1
          /\ UNCHANGED << nBackfill, walSalt >>
  /\ frameNumber' = frameNumber + 1
  /\ writeLock' = "notTaken"
  /\ UNCHANGED << db, checkpoint_vars >>

CheckpointCopyHeader ==
  /\ checkpointState = "notStarted"
  /\ safeMxFrame' = mxFrame
  /\ pWalSalt' = walSalt
  /\ checkpointState' = "copiedHeader"
  /\ UNCHANGED << wal,
        nBackfill,
        db,
        mxFrame,
        frameNumber,
        walSalt,
        writeLock
     >>

StartCheckpoint ==
  /\ checkpointState = "copiedHeader"
  /\ checkpointState' =
       IF nBackfill < safeMxFrame THEN "waitingForLock" ELSE "notStarted"
  /\ UNCHANGED << wal,
        nBackfill,
        db,
        mxFrame,
        frameNumber,
        safeMxFrame,
        walSalt,
        pWalSalt,
        writeLock
     >>

Checkpoint ==
  /\ checkpointState = "waitingForLock"
  /\ db' = db \union {wal[j]: j \in nBackfill + 1 .. Len(wal)}
  /\ nBackfill' = safeMxFrame
  /\ safeMxFrame' = 0
  /\ pWalSalt' = 0
  /\ checkpointState' = "notStarted"
  /\ UNCHANGED << mxFrame, wal, frameNumber, walSalt, writeLock >>

NoPageILost == \A f \in 1 .. Cardinality(db): f \in db
====