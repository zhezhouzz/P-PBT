val ( == ) : 'a -> 'a -> bool

(** message from env to panel *)

(* event: init *)
val eCoffeeMachineUser : unit [@@gen]

let eCoffeeMachineUser = (allA, ECoffeeMachineUser true, [| EWarmUpReq true |])

(* event: make espresso button pressed *)
val eEspressoButtonPressed : unit [@@gen]

let eEspressoButtonPressed =
  [|
    ( (allA;
       ECoffeeMakerReady true;
       starA (anyA - ECoffeeMakerError true)),
      EEspressoButtonPressed true,
      [| EGrindBeansReq true |] );
  |]

(* (\* event: steamer button turned off *\) *)
(* val eSteamerButtonOff : unit [@@gen] *)

(* (\* event: steamer button turned on *\) *)
(* val eSteamerButtonOn : unit [@@gen] *)

(* (\* event: door opened to empty grounds *\) *)
(* val eOpenGroundsDoor : unit [@@gen] *)

(* (\* event: door closed after emptying grounds *\) *)
(* val eCloseGroundsDoor : unit [@@gen] *)

(* (\* event: reset coffee maker button pressed *\) *)
(* val eResetCoffeeMaker : unit [@@gen] *)

(** message from panel to env *)

(* event: error message from panel to the user
   1: NotWarmedUp,
   2: Ready,
   3: NoBeansError,
   4: NoWaterError
*)

val eCoffeeMakerError :
  < st : (notWaredUp * ready * noBeansError * noWaterError[@status]) >
[@@obsRecv]

let eCoffeeMakerError
    ?l:(x =
        (true
          : [%v: (notWaredUp * ready * noBeansError * noWaterError[@status])]))
    =
  (allA, ECoffeeMakerError (st == x), [||])

(* event: completed brewing and pouring coffee *)
val eCoffeeMakerCompleted : unit [@@obsRecv]

let eCoffeeMakerCompleted = (allA, ECoffeeMakerCompleted true, [||])

(* event: coffee machine is ready *)
val eCoffeeMakerReady : unit [@@obsRecv]

let eCoffeeMakerReady = (allA, ECoffeeMakerReady true, [||])

(** internal messages *)

(* event: warmup request when the coffee maker starts or resets *)
val eWarmUpReq : unit [@@obs]

let eWarmUpReq = (allA, EWarmUpReq true, [| EWarmUpCompleted true |])

(* event: grind beans request before making coffee *)
val eGrindBeansReq : unit [@@obs]

let eGrindBeansReq =
  [|
    (allA, EGrindBeansReq true, [| ENoBeansError true |]);
    (allA, EGrindBeansReq true, [| EGrindBeansCompleted true |]);
  |]

(* event: start brewing coffee *)
val eStartEspressoReq : unit [@@obs]

let eStartEspressoReq =
  [|
    (allA, EStartEspressoReq true, [| ENoWaterError true |]);
    (allA, EStartEspressoReq true, [| EEspressoCompleted true |]);
  |]

(* (\* val start steamer *\) *)
(* val eStartSteamerReq : unit [@@obs] *)

(* (\* event: stop steamer *\) *)
(* val eStopSteamerReq : unit [@@obs] *)

(* Responses from the coffee maker to the controller *)
(* event: completed grinding beans *)
val eGrindBeansCompleted : unit [@@obs]

let eGrindBeansCompleted =
  (allA, EGrindBeansCompleted true, [| EStartEspressoReq true |])

(* event: completed brewing and pouring coffee *)
val eEspressoCompleted : unit [@@obs]

let eEspressoCompleted =
  (allA, EEspressoCompleted true, [| ECoffeeMakerCompleted true |])

(* event: warmed up the machine and read to make coffee *)
val eWarmUpCompleted : unit [@@obs]

let eWarmUpCompleted =
  (allA, EWarmUpCompleted true, [| ECoffeeMakerReady true |])

(* Error messages from the coffee maker to control panel or controller*)
(* event: no water for coffee, refill water! *)
val eNoWaterError : unit [@@obs]

let eNoWaterError =
  ( allA,
    ENoWaterError true,
    [|
      ECoffeeMakerError
        (st
        == ("NoWaterError"
             : (notWaredUp * ready * noBeansError * noWaterError[@status])));
    |] )

(* event: no beans for coffee, refill beans! *)
val eNoBeansError : unit [@@obs]

let eNoBeansError =
  ( allA,
    ENoBeansError true,
    [|
      ECoffeeMakerError
        (st
        == ("NoBeansError"
             : (notWaredUp * ready * noBeansError * noWaterError[@status])));
    |] )

(** Goal *)

let[@goal] no_no_water_error =
  not
    (allA;
     ECoffeeMakerError
       (st
       == ("NoWaterError"
            : (notWaredUp * ready * noBeansError * noWaterError[@status])));
     allA)
