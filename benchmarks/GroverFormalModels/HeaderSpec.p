type Segment = machine;
event eLsnProgress: tLsn;
event eReadLogRecordsProcessResult: tReadLogRecordsProcessResult;
event eWriteLogRecordsProcessResult: tWriteLogRecordsProcessResult;
event eAllRequestsProcessed: (numReadRequests: int, numWriteRequests: int);
event eSeedUlrs;
event eIsSeedingCompleteReq: machine;
event eIsSeedingCompleteRes: (res: bool);
event eGenerateRequests;
type tLsn = int;
type tLogRecord = (lsn: tLsn, page: string, backlink: tLsn);
type tQuorumSet = (fullSegments: set[Segment], tailSegments: set[Segment], quorumPolicy: tQuorumPolicy);
type tQuorumPolicy = (fullSegmentsWriteQuorumSize: int, allSegmentsWriteQuorumSize: int);
type tQuorumShape = (azCount: int, fullSegmentsPerAz: int, tailSegmentsPerAz: int);
type tEphMetadata = (pggcl: tLsn, pgmprl: tLsn);
type tPgEpochData = (pgId: string, volId: string, epoch: int, currentQs: tQuorumSet, transitionQs: tQuorumSet);
type tPg = (id: string, pgEpochData: tPgEpochData, ephMetadata: tEphMetadata, targetQuorumShape: tQuorumShape, targetAzs: set[string], droppedAz: string);
type tReadLogRecordsProcessResult = (req: tReadLogRecordsReq, result: bool);
type tWriteLogRecordsProcessResult = (req: tWriteLogRecordsReq, result: bool);
type tReadLogRecordsReq = (rId: string, client: machine, startLsn: tLsn);
type tWriteLogRecordsReq = (rId: string, client: machine, ulrs: seq[tLogRecord], ephMetadata: tEphMetadata);
event ePeeringComplete;
event eRepairComplete: (epoch: int, numCurrentQs: int, numTransitionQs: int);
event eRepairRevert: tPg;
event eSeedLsnReq: (client: machine, givenLsn: tLsn);
event eSeedLsnRes: (resLsn: tLsn);
event eRequestRepair;

type tRId = int;

REQ SeedLsnReq = eSeedLsnReq : (givenLsn: tLsn);
RSP SeedLsnRes = eSeedLsnRes : (resLsn: tLsn);

REQ SeedUlrs = eSeedUlrs;

REQ IsSeedingCompleteReq = eIsSeedingCompleteReq;
RSP IsSeedingCompleteRes = eIsSeedingCompleteRes: (res: bool);

REQ GenerateRequests = eGenerateRequests;
REQ RequestRepair = eRequestRepair;

HIDDEN AllRequestsProcessed = eAllRequestsProcessed : (numReadRequests: int, numWriteRequests: int);
HIDDEN LsnProgress = eLsnProgress;
HIDDEN ReadLogRecordsProcessResult = eReadLogRecordsProcessResult : (rId: tRId, result: bool);
HIDDEN WriteLogRecordsProcessResult = eWriteLogRecordsProcessResult : (rId: tRId, result: bool);
HIDDEN PeeringComplete = ePeeringComplete;
HIDDEN RepairComplete = eRepairComplete : (epoch: int, numCurrentQs: int, numTransitionQs: int);
HIDDEN RepairRevert = eRepairRevert;