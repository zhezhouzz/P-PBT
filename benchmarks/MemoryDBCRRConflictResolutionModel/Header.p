/* there are 3 type of values:
   String (e.g., indeed, int)
   Hash (e.g., a hashtable)
   Set (e.g., a set)
  */

enum VType {
    String,
    Hash,
    Set
}

/* In this model we assume there are value are (VType, value) */

type value = int /* uninterpreted sort, or just int */

type tKey = int /* will be converted into string by P */

type seqNbr = int /* if seqNbr == -1, it means the key is deleted. */

hidden event eUpdateKeyValueTimestamp (nodeId: int, key: tKey, seqNbr: seqNbr, vType: VType, value: value);

/*
 * Define command used in this modeling.
 *      GET: read a key. Fail if key does not exit. (Not used, as eventual consistency validation is done on key/value store directly)
 *      SET: write a key to a new string (string literal or counter) value. Always succeed. (Blind write)
 *      INCR:
 *          increase an integer value based on the keys' current value. (Delta update)
 *          If key does not exist, create it with 0 value, then increase the integer amount. (Blind write)
 *      SADD: add a member to a Set data structure.
 *      SREM: remove a member from a Set data structure.
 *      DEL: delete an existing key. Fail if key does not exist. Use element-level LWW for Collection datatypes. (Blind write)
 *      FLUSHALL: flush all keys up to an upper sequence number limit.
 *      HSET: set a key to a hash with a random num of fields.
 *      HDEL: delete a random field from a hash key.
 */

/* There are 10 types of commands.
   Why set cammand set a string?

   GET(key: tKey)
   SET(key: tKey, value: (String, int))
   INCR(key: tKey, value: (String, int))
   HSET(key: tKey, value: int) -- the number of fields
   HDEL(key: tKey, value: int) -- the index
   SADD(key: tKey, value: tKey)
   SREM(key: tKey, value: tKey)
   DEL(key: tKey)
   AMZ_DEL(key: tKey)
   FLUSHALL()
  */


enum tStatus {
    SUCCESS,
    FAILURE
}

/* most of command only return status, and don't indicate about the key */

/* it seems that get will not trigger eUpdateKeyValueTimestamp. */
event {
  request eGetReq (nodeId: int, key: tKey)  ;
  response eGetResp (nodeId: int, executionResult: tStatus) ;
  }

event {
  request eSetReq (nodeId: int, key: tKey, v: int)  ;
  response eSetResp (nodeId: int, executionResult: tStatus) ;
  }

event {
  request eIncrReq (nodeId: int, key: tKey, v: int)  ;
  response eIncrResp (nodeId: int, executionResult: tStatus) ;
  }

event {
  request eHsetReq (nodeId: int, key: tKey, num: int)  ;
  response eHSetResp (nodeId: int, executionResult: tStatus) ;
  }

event {
  request eHdelReq (nodeId: int, key: tKey, field: int)  ;
  response eHDelResp (nodeId: int, executionResult: tStatus) ;
  }

event {
  request eSaddReq (nodeId: int, key: tKey, elem: tKey)  ;
  response eSaddResp (nodeId: int, executionResult: tStatus) ;
  }

event {
  request eSremReq (nodeId: int, key: tKey, elem: tKey)  ;
  response eSremResp (nodeId: int, executionResult: tStatus) ;
  }

event {
  request eDelReq (nodeId: int, key: tKey)  ;
  response eDelResp (nodeId: int, executionResult: tStatus) ;
  }

event {
  request eAMZDelReq (nodeId: int, key: tKey)  ;
  response eAMZDelResp (nodeId: int, executionResult: tStatus) ;
  }

event {
  request eFlushAllReq (nodeId: int)  ;
  response eFlushAllResp (nodeId: int, executionResult: tStatus) ;
  }
