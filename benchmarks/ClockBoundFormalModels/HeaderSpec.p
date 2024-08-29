type tTime = int;
type tClockBoundTime = (earliest: tTime, latest: tTime);

// Request: ClockBound TimeNow
type tGetClockBoundTimeNowReq = (requester: machine, requestId: int, nodeId: tId);
event eGetClockBoundTimeNowReq: tGetClockBoundTimeNowReq;

// Response: ClockBound TimeNow
type tGetClockBoundTimeNowRsp = (requestId: int, now: tClockBoundTime);
event eGetClockBoundTimeNowRsp: tGetClockBoundTimeNowRsp;

type tMonitorGetClockBoundTimeNowRsp = (requestId: int, now: tClockBoundTime, ghost_trueTime: tTime, localClock: machine, nodeId: tId);
event eMonitorGetClockBoundTimeNowRsp: tMonitorGetClockBoundTimeNowRsp;

type tId = int;
type rId = int;
REQ GetClockBoundTimeNowReq = eGetClockBoundTimeNowReq : (requestId: rId, nodeId: tId);
RSP GetClockBoundTimeNowRsp = eGetClockBoundTimeNowRsp : (requestId: rId, earliest: tTime, latest: tTime);
HIDDEN MonitorGetClockBoundTimeNowRsp = eMonitorGetClockBoundTimeNowRsp : (requestId: rId, earliest: tTime, latest: tTime, ghost_trueTime: tTime, nodeId: tId);