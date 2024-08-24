spec LastStatusEq (nodeId: int) (key: tKey) (seqNbr: seqNbr) (vType: VType) (value: value) {
  atom (a: eUpdateKeyValueTimestamp) :: #nodeId == nodeId && #key == key && #seqNbr == seqNbr && #vType == vType && #value == value
  atom (b: eUpdateKeyValueTimestamp) :: #nodeId == nodeId && #key == key
  regex .* ~ a ~ (. - b)*
  }

/* It is kind of hard to detect the nested equality of datatype -- however, if it is eventually consistency, the elements in collection is already checked by other keys.
  */
spec LastStatusNeq (nodeId: int) (key: tKey) (seqNbr: seqNbr) (vType: VType) (value: value) {
  atom (a: eUpdateKeyValueTimestamp) :: #nodeId == nodeId && #key == key && not (#vType == vType && #seqNbr == seqNbr && #value == value)
  atom (b: eUpdateKeyValueTimestamp) :: #nodeId == nodeId && #key == key
  regex (.* ~ a ~ (. - b)*) || (. - b)*
  }

/* It means the client need to send massages to different nodes, the send wrapper will control is via nodeId */
spec EventualConsistencyInvariant (nodeId1: int) (nodeId2: int) (key: tKey) (seqNbr: seqNbr) (vType: VType) (value: value) {
  global nodeId1 != nodeId2
  regex (LastStatusEq nodeId1 key seqNbr vType value) && (LastStatusEq nodeId2 key seqNbr vType value)
}
