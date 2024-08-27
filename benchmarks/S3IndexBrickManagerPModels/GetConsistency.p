/* mantianed by the successed response of put/get/delete, must have larger sqr */
spec SuccStateOfKey (key: tByteString) (sqr: int) (recordType: enum) (val: int) = {
  atom (respEq: eBrickGetResp | eBrickPutResp | eBrickDeleteResp) :: #key == key && #sqr == sqr && #recordType == recordType && #val == val && status == SUCCESS;
  atom (respGT: eBrickGetResp | eBrickPutResp | eBrickDeleteResp) :: #key == key && #sqr > sqr && status == SUCCESS;
  regex (not (.* ~ respGt ~ .*)) && (.* ~ respEq ~ .*)
  }

/* mantianed by the request of put/delete; don't consider sqr and there is no status */
spec PendingStateOfKey (key: tByteString) (sqr: int) (recordType: enum) (val: int) = {
  atom (respEq: eBrickPutReq | eBrickDeleteResp) :: #key == key && #sqr == sqr && #recordType == recordType && #val == val;
  atom (respOther: eBrickPutReq | eBrickDeleteResp) :: #key == key;
  regex (.* ~ respEq ~ (. \ respOther)*)
  }

spec SuccStateWhenReq (rId: int) (key: tByteString) (sqr: int) (recordType: enum) (val: int) = {
  atom (req: eBrickGetReq) :: #key == key && #rId == rId
  regex ((SuccStateOfKey key sqr recordType val) ~ req ~ .*)
  }

spec SuccOrPendingStateWhenReq (rId: int) (key: tByteString) (sqr: int) (recordType: enum) (val: int) = {
  atom (req: eBrickGetReq) :: #key == key && #rId == rId
  regex ((SuccStateOfKey key sqr recordType val || PendingStateOfKey key sqr recordType val) ~ req ~ .*)
  }

/* we don't check the mono of sqr for TOMBSTONE? */
spec GetConsistency1 (rId: int) (key: tByteString) (sqr: int) (recordType: enum) (val: int) = {
  atom (respWrong : eBrickGetResp) :: #key == key && #rId == rId && #sqr < sqr && not (#recordType == TOMBSTONE)
  regex not ((SuccStateWhenReq key sqr recordType val) ~ respWrong ~ .*);
  }

spec GetConsistency2 (rId: int) (key: tByteString) (sqr: int) (recordType: enum) (val: int) = {
  atom (respWrong : eBrickGetResp) :: #key == key && #rId == rId && not (#sqr == sqr && #recordType == recordType && #val == val)
  regex not ((SuccOrPendingStateWhenReq rId key sqr recordType val) ~ respWrong ~ .*);
  }

spec GetEventually (rId: int) = {
  atom (req: eBrickGetReq) :: #rId == rId
  atom (resp: eBrickGetResp) :: #rId == rId
  regex not (.* ~ req ~ (. \ resp)*)
  }
