/* the rId in request are unique */
spec rIdUniqueReq (rId: int) {
  atom (rep: eBrickPutReq | eBrickGetReq | eBrickDeleteReq) :: #rId == rId;
  regex (not (.* ~ rep ~ .* ~ rep .*))
}

/* the rId in response are unique */
spec rIdUniqueResp (rId: int) {
  atom (resp: eBrickPutResp | eBrickGetResp | eBrickDeleteResp) :: #rId == rId;
  regex (not (.* ~ resp ~ .* ~ resp .*))
}

/* the response is trigger by request */
spec todo                       ;
