event eSpec_CRead: (seqNo: int, timestamp: int);
event eSpec_ECRead: (seqNo: int);
event eSpec_DataRecordCommittedOnLeader: (node: int, committedSeqNo: int, committedGeneration: int, timestamp: int);
event eSpec_DataRecordCommittedToJournal: (committedSeqNo: int, committedGeneration: int, timestamp: int);

spec currJournalCommittedSequenceNo (committedSeqNo: int) = {
  atom (a: eSpec_DataRecordCommittedToJournal) :: #committedSeqNo == committedSeqNo
  atom (c: eSpec_DataRecordCommittedToJournal) :: true
  regex (.* ~ a ~ (. \ c)*)
}

spec currJournalCommittedTimestep (committedSeqNo: int, timestamp: int) = {
  atom (a: eSpec_DataRecordCommittedToJournal) :: #committedSeqNo == committedSeqNo && #timestamp == timestamp
  atom (c: eSpec_DataRecordCommittedToJournal) :: #committedSeqNo == committedSeqNo
  regex (.* ~ a ~ (. \ c)*)
}

spec journalCommittedSequenceNoIncr (committedSeqNo: int) = {
  atom (b: eSpec_DataRecordCommittedToJournal) :: not (#committedSeqNo == committedSeqNo + 1)
  regex not ((currJournalCommittedSequenceNo committedSeqNo) ~ b ~ .*)
}

spec DataRecordCommittedOnLeaderLt (committedSeqNo: int) = {
  atom (b: eSpec_DataRecordCommittedOnLeader) :: #committedSeqNo > committedSeqNo
  regex not ((currJournalCommittedSequenceNo committedSeqNo) ~ b ~ .*)
}

spec ECReadConsistency (seqNo: int) = {
  atom (b: eSpec_ECRead:) :: #seqNo > seqNo
  regex not ((currJournalCommittedSequenceNo seqNo) ~ b ~ .*)
}

spec CReadConsistency1 (seqNo: int,) = {
  atom (b: eSpec_ECRead:) :: #seqNo > seqNo
  regex (not ((currJournalCommittedSequenceNo seqNo) ~ b ~ .*))
}

spec CReadConsistency2 (seqNo: int, timestamp: int) = {
  atom (b: eSpec_ECRead:) :: #seqNo == seqNo && #timestamp < timestamp 
  regex (not ((currJournalCommittedTimestep seqNo timestamp) ~ b ~ .*))
}