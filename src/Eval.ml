(* evaluation *)
type action =
  | CSkip
  | CAssert
  | CSet
  | CWhile1 | CWhile2 | CWhile3
  | CIf1 | CIf2
  | CSeq1 | CSeq2

let atomic_ops = function
  | CSkip | CSet | CAssert -> 1
  | _ -> 0

module type QMONOID = sig
  type t
  val lift: int -> t
  val zero: t
  val concat: t -> t -> t
end

module Eval(QMon: QMONOID) = struct
  open Parse
  open QMon

  module Heap =
    Map.Make(struct type t = id  let compare = compare end)

  type value = int and heap = value Heap.t

  let (-$) c1 c2 heap =
    let (heap', cost1) = c1 heap in
    let (heap'', cost2) = c2 heap' in
    (heap'', concat cost1 cost2)

  let pay price heap = (heap, lift price)

  let guard f c1 c2 heap =
    if f heap then c1 () heap else c2 () heap

  let value v h =
    match v with
    | VNum n -> n
    | VId id -> try Heap.find id h with Not_found -> 0

  let inc id op v heap =
    let res =
      match op with
      | OPlus -> value (VId id) heap + value v heap
      | OMinus -> value (VId id) heap - value v heap
    in (Heap.add id res heap, zero)

  let set id v heap =
    (Heap.add id (value v heap) heap, zero)

  let test (C (l1, cmp, l2)) heap =
    let rec lsum heap = function
      | LAdd (l1, l2) -> lsum heap l1 + lsum heap l2
      | LSub (l1, l2) -> lsum heap l1 - lsum heap l2
      | LMult (k, l) -> k * lsum heap l
      | LVar v -> value v heap in
    begin match cmp with
    | CLe -> ( <= ) | CGe -> ( >= )
    | CLt -> ( < ) | CGt -> ( > )
    end (lsum heap l1) (lsum heap l2)

  exception ProgramFailure of prog

  let eval cost =
    let pay act = pay (cost act) in
    let rec eval = function
      | PSkip _ -> pay CSkip
      | PSeq (p1, p2, _) -> pay CSeq1 -$ eval p1 -$ pay CSeq2 -$ eval p2
      | PInc (v1, op, v2, _) -> pay CSet -$ inc v1 op v2
      | PSet (v1, v2, _) -> pay CSet -$ set v1 v2
      | PWhile (cond, p, _) as ploop ->
        guard (test cond)
          (fun () -> pay CWhile1 -$ eval p -$ pay CWhile2 -$ eval ploop)
          (fun () -> pay CWhile3)
      | PAssert (c, _) as p ->
        guard (test c)
          (fun () -> pay CAssert)
          (fun () -> raise (ProgramFailure p))
      | PIf (c, p1, p2, _) ->
        guard (test c)
          (fun () -> eval p1)
          (fun () -> eval p2)
    in eval

  let empty_heap = Heap.empty

  let print_heap =
    Heap.iter (Printf.printf "%s -> %d\n")
end


(* sample metrics *)

module QMUnit: QMONOID = struct
  type t = unit
  let lift _ = ()
  let zero = ()
  let concat _ _ = ()
end

module QMInt: (QMONOID with type t = int) = struct
  type t = int
  let lift x = x
  let zero = 0
  let concat a b = a + b
end


(* testing *)

let _ =
  match try Some Sys.argv.(1) with _ -> None with
  | Some "-teval" ->
    let module E = Eval(QMInt) in
    let p = Parse.pa_prog stdin in
    begin try
      let (hfinal, cost) = E.eval atomic_ops p E.empty_heap in
      E.print_heap hfinal;
      Printf.printf "evaluation cost: %d\n" cost
    with E.ProgramFailure p ->
      Printf.printf "program failure on: "; Parse.pp_prog p;
      exit 1
    end
  | _ -> ()
