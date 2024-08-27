spec LastStatusEq (nodeId1: tId) (key1: tKey) (seqNbr1: tSeqNbr) (valueType1: ValueType) (val1: tVal) {
  atom (a: UpdateKeyValueTimestamp) :: #nodeId == nodeId1 && #key == key1 && #seqNbr == seqNbr1 && #valueType == valueType1 && #val == val1;
  atom (b: UpdateKeyValueTimestamp) :: #nodeId == nodeId1 && #key == key1;
  regex .* ~ a ~ (. - b)*
  }

/* It is kind of hard to detect the nested equality of datatype -- however, if it is eventually consistency, the elements in collection is already checked by other keys.
  */
spec LastStatusNeq (nodeId1: tId) (nodeId2: tId) (key1: tKey) (seqNbr1: tSeqNbr) (valueType1: ValueType) (val1: tVal) {
  atom (a: UpdateKeyValueTimestamp) :: (not (#nodeId == nodeId1)) && #nodeId == nodeId2 && #key == key1 && not (#valueType == valueType1 && #seqNbr == seqNbr1 && #val == val1);
  atom (b: UpdateKeyValueTimestamp) :: (not (#nodeId == nodeId1)) && #nodeId == nodeId2 && #key == key1;
  regex (.* ~ a ~ (. - b)*)
  }

/* It means the client need to send massages to different nodes, the send wrapper will control is via nodeId */
spec EventualConsistencyInvariant (nodeId1: tId) (nodeId2: tId) (key1: tKey) (seqNbr1: tSeqNbr) (valueType1: ValueType) (val1: tVal) {
  regex not ((LastStatusEq nodeId1 key1 seqNbr1 valueType1 val1) && (LastStatusNeq nodeId1 nodeId2 key1 seqNbr1 valueType1 val1))
}

spec ax1 (nodeId1: tId) (nodeId2: tId) (key1: tKey) (seqNbr1: tSeqNbr) (valueType1: ValueType) (val1: tVal) {
  atom (a: ClientReq) :: #nodeId == nodeId1 && #key == key1 && #val == val1 && commandType == (1: CommandType);
  atom (b: UpdateKeyValueTimestamp) :: #nodeId == nodeId1 && #key == key1 && #valueType == valueType1 && #val == val1;
  regex ((. \ b)* ~ a ~ b ~ (. \ b)*) || (. \ b)*
}

spec ax2 (nodeId1: tId) (nodeId2: tId) (key1: tKey) (seqNbr1: tSeqNbr) (valueType1: ValueType) (val1: tVal) {
  atom (a: ClientReq) :: (not (#nodeId == nodeId1)) && #nodeId == nodeId2 && #key == key1 && #val == val1 && commandType == (1: CommandType);
  atom (b: UpdateKeyValueTimestamp) :: #nodeId == nodeId2 && #key == key1 && #valueType == valueType1 && #val == val1;
  regex ((. \ b)* ~ a ~ b ~ (. \ b)*) || (. \ b)*
}

spec ax3 (nodeId1: tId) (nodeId2: tId) (key1: tKey) (seqNbr1: tSeqNbr) (valueType1: ValueType) (val1: tVal) {
  atom (a: ClientReq) :: true;
  atom (b: UpdateKeyValueTimestamp) :: true;
  atom (c: ClientResp) :: true;
  regex (a ~ b ~ c)* || ((a ~ b ~ c)* ~ a) || ((a ~ b ~ c)* ~ a ~ b)
}

generator SynClient {
  scope = [ClientReq, UpdateKeyValueTimestamp, ClientResp];
  axiom = [ax1, ax2, ax3];
  config = [tKey, tVal];
  violation = EventualConsistencyInvariant;
  step = 6;
}

