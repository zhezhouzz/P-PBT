spec AllRequestsSucceed {
  atom (a: ReadLogRecordsProcessResult | WriteLogRecordsProcessResult) :: not #result;
  regex not (.* ~ a ~ .*)
}

spec AllRequestsProcessed {
  atom (a: AllRequestsProcessed) :: not (#numReadRequests == 0 && #numWriteRequests == 0);
  regex not (.* ~ a ~ .*)  
}

spec AppearPeeringComplete0 {
  atom (a: PeeringComplete) :: true;
  regex (. \ a)*
}

spec AppearPeeringComplete1 {
  atom (a: PeeringComplete) :: true;
  regex (. \ a)* ~ a ~ (. \ a)*
}

spec AppearPeeringComplete3 {
  atom (a: PeeringComplete) :: true;
  regex (. \ a)* ~ a ~ (. \ a)* ~ a ~ (. \ a)* ~ a ~ (. \ a)*
}

spec AppearPeeringComplete5More {
  atom (a: PeeringComplete) :: true;
  regex (. \ a)* ~ a ~ (. \ a)* ~ a ~ (. \ a)* ~ a ~ (. \ a)* ~ a ~ (. \ a)* ~ a ~ .* 
}

spec RepairCompletesPeeringCount {
  atom (b: RepairComplete) :: true;
  regex not ((AppearPeeringComplete0 || AppearPeeringComplete1 || AppearPeeringComplete3 ||  AppearPeeringComplete5More) ~ b ~ .*)
}

spec RepairCompletesPg {
  atom (a: RepairComplete) :: not ((#epoch == 2 || #epoch == 4) && #numCurrentQs > 0 && #numTransitionQs == 0);
  regex not (.* ~ a ~ .*)
}

spec RepairCompletesLiveness {
  atom (a: RepairRevert) :: true;
  atom (b: RepairComplete) :: true;
  regex not (.* ~ a ~ (. \ b)*)
}

spec dummyAx (id: tRId) {
  regex .*
}

spec dummy (id: tRId) {
  regex . ~ . ~ .
}

generator SynClient {
  scope = [SeedLsnReq, SeedLsnRes, SeedUlrs, IsSeedingCompleteReq, IsSeedingCompleteRes, GenerateRequests, RequestRepair];
  axiom = [dummyAx];
  config = [];
  violation = dummy;
  step = 3;
}