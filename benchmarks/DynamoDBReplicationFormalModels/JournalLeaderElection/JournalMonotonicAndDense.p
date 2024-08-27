event eSpec_DataRecordCommittedToJournal: (committedSeqNo: int, committedGeneration: int, timestamp: int);

spec currJournalCommittedState (committedSeqNo: int) (committedGeneration: int) (timestamp: int) = {
  atom (a: eSpec_DataRecordCommittedToJournal) :: #committedSeqNo == committedSeqNo && #committedGeneration == committedGeneration && #timestamp == timestamp 
  atom (c: eSpec_DataRecordCommittedToJournal) :: true
  regex (.* ~ a ~ (. \ c)*)
}

spec JournalMonotonicAndDense (committedSeqNo: int) (committedGeneration: int) (timestamp: int) = {
  atom (b: eSpec_ECRead:) :: not (#committedSeqNo == committedSeqNo + 1 && #committedGeneration >= committedGeneration && #timestamp > timestamp)
  regex not ((currJournalCommittedState committedSeqNo committedGeneration timestamp) ~ b ~ .*)
}