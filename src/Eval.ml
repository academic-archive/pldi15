(* evaluation *)
type action =
  | CSkip
  | CAssert
  | CSet
  | CWhile1 | CWhile2 | CWhile3
  | CIf1 | CIf2
  | CSeq1 | CSeq2

module type METRIC = sig
  type t
  val cost: action -> t
  val free: t
  val concat: t -> t -> t
end

module Eval(M: METRIC) = struct
  open Parse
  open M

  module Heap =
    Map.Make(struct type t = id  let compare = compare end)

  type value = int and heap = value Heap.t

  let (-$) c1 c2 heap =
    let (heap', cost1) = c1 heap in
    let (heap'', cost2) = c2 heap' in
    (heap'', concat cost1 cost2)

  let pay act heap = (heap, cost act)

  let guard f c1 c2 heap =
    if f heap then c1 () heap else c2 () heap

  let value v h =
    match v with
    | VNum n -> n
    | VId id -> try Heap.find id h with _ -> 0

  let inc id op v heap =
    let res =
      match op with
      | OPlus -> value (VId id) heap + value v heap
      | OMinus -> value (VId id) heap - value v heap
    in (Heap.add id res heap, free)

  let set id v heap =
    (Heap.add id (value v heap) heap, free)

  let test (Cond (v1, v2, k)) heap =
    value v1 heap - value v2 heap > k

  exception ProgramFailure of prog

  let rec eval = function
    | PSkip -> pay CSkip
    | PSeq (p1, p2) -> pay CSeq1 -$ eval p1 -$ pay CSeq2 -$ eval p2
    | PInc (v1, op, v2) -> pay CSet -$ inc v1 op v2
    | PSet (v1, v2) -> pay CSet -$ set v1 v2
    | PWhile (cond, p) as ploop ->
      guard (test cond)
        (fun () -> pay CWhile1 -$ eval p -$ pay CWhile2 -$ eval ploop)
        (fun () -> pay CWhile3)
    | PAssert c as p ->
      guard (test c)
        (fun () -> pay CAssert)
        (fun () -> raise (ProgramFailure p))

  let empty_heap = Heap.empty

  let print_heap =
    Heap.iter (Printf.printf "%s -> %d\n")
end


(* sample metrics *)

module CostFree: METRIC = struct
  type t = unit
  let cost _ = ()
  let free = ()
  let concat _ _ = ()
end

module AtomicOps: (METRIC with type t = int) = struct
  type t = int
  let cost = function
    | CSkip | CSet | CAssert -> 1
    | _ -> 0
  let free = 0
  let concat a b = a + b
end


(* testing *)

let _ =
  match try Some Sys.argv.(1) with _ -> None with
  | Some "-teval" ->
    let module E = Eval(AtomicOps) in
    let p = Parse.prog stdin in
    begin try
      let (hfinal, cost) = E.eval p E.empty_heap in
      E.print_heap hfinal;
      Printf.printf "evaluation cost: %d\n" cost
    with E.ProgramFailure p ->
      Printf.printf "program failure on: "; Parse.pp_prog p;
      exit 1
    end
  | _ -> ()
