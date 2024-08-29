spec ClockBoundInvariantsSanityCheck {
  atom (a: MonitorGetClockBoundTimeNowRsp) :: not ((#earliest < #ghost_trueTime || #earliest == #ghost_trueTime) && (#ghost_trueTime < #latest || #ghost_trueTime == #latest));
  regex not (.* ~ a ~ .*)
}

spec ClockBoundInvariantsGTimeIncr (gtime: tTime) {
  atom (a: MonitorGetClockBoundTimeNowRsp) :: #ghost_trueTime == gtime;
  atom (b: MonitorGetClockBoundTimeNowRsp) :: #ghost_trueTime < gtime;
  regex not (.* ~ a ~ .* ~ b ~ .*)
}

/*
  Invariants for ClockBound:

  Let Ti = (Ei, Li) where Ei represents the earliest and Li represents the latest
  time bounds returned by the ClockBoundTimeNow API when invoked at time Ti.

  Invariant 1:
  For two ClockBoundTimeNow invocations at time T1 and T2 on the SAME NODE (i.e., same client).
  If T2 happened after T1, i.e., T2 > T1, then E2 >= E1.

  >> The above invariant ensures that time must always be increasing at the local clock.

  Invariant 2:
  For two ClockBoundTimeNow invocations at time T1 and T2 (could be on DIFFERENT or SAME node).
  If T2 > T1 (T2 happened after T1), then  L2 > E1.


  Invariant 3 (derived from 2):
  For two ClockBoundTimeNow invocations at time T1 and T2 (could be on DIFFERENT or SAME nodes).
  If L1 < E2 then T1 < T2 i.e. T1 must definitely have happened before T2.
*/

spec ClockBoundInvariants1 (id: tId) (gtime: tTime) (tm: tTime) {
  atom (a: MonitorGetClockBoundTimeNowRsp) :: #nodeId == id && #ghost_trueTime == gtime && #earliest == tm;
  atom (b: MonitorGetClockBoundTimeNowRsp) :: #nodeId == id && (gtime < #ghost_trueTime) && #earliest < tm;
  regex not (.* ~ a ~ .* ~ b ~ .*) 
}

spec ClockBoundInvariants2 (gtime: tTime) (tm: tTime) {
  atom (a: MonitorGetClockBoundTimeNowRsp) :: #ghost_trueTime == gtime && #earliest == tm;
  atom (b: MonitorGetClockBoundTimeNowRsp) :: (gtime < #ghost_trueTime) && (#latest < tm || #latest == tm);
  regex not (.* ~ a ~ .* ~ b ~ .*) 
}

spec ClockBoundInvariants2Overlap (gtime: tTime) (tmE: tTime) (tmL: tTime) {
  atom (a: MonitorGetClockBoundTimeNowRsp) :: #ghost_trueTime == gtime && #earliest == tmE && #latest == tmL;
  atom (noOverlap: MonitorGetClockBoundTimeNowRsp) :: #ghost_trueTime == gtime && (not ((#earliest <= tmE && #latest >= tmL) || (#earliest > tmE && tmL >= #latest)));
  regex not (.* ~ a ~ .* ~ noOverlap ~ .*) 
}

spec ClockBoundInvariants3 (gtime: tTime) (tm: tTime) {
  atom (a: MonitorGetClockBoundTimeNowRsp) :: #ghost_trueTime == gtime && #latest == tm;
  atom (b: MonitorGetClockBoundTimeNowRsp) :: (#ghost_trueTime == gtime) && (#earliest > tm);
  regex not (.* ~ a ~ .* ~ b ~ .*) 
}

spec dummyAx (id: tId) (gtime: tTime) (tm: tTime) {
  regex .*
}

spec dummy (id: tId) (gtime: tTime) (tm: tTime) {
  regex . ~ . ~ .
}

generator SynClient {
  scope = [MonitorGetClockBoundTimeNowRsp, GetClockBoundTimeNowReq, GetClockBoundTimeNowRsp];
  axiom = [dummyAx];
  config = [tId];
  violation = dummy;
  step = 3;
}