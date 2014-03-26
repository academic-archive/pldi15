(* evaluation *)
module type METRIC = sig
  type t
  type action =
    | CSkip
    | CSet
    | CAssert
    | CWhile1 | CWhile2 | CWhile3
    | CIf1 | CIf2
    | CSeq1 | CSeq2
  val cost: action -> t
  val free: t
  val concat: t -> t -> t
end

module Eval(M: METRIC) = struct
  open Parse
  open M

  module Heap =
    Map.Make(struct type t = var  let compare = compare end)

  type value = int and heap = value Heap.t

  let (-$) c1 c2 heap =
    let (heap', cost1) = c1 heap in
    let (heap'', cost2) = c2 heap' in
    (heap'', concat cost1 cost2)

  let pay act heap = (heap, cost act)

  let guard f c1 c2 heap =
    if f heap then c1 () heap else c2 () heap

  let value v h =
    if v.[0] = '$'
      then int_of_string (String.sub v 1 (String.length v - 1))
      else try Heap.find v h with _ -> 0

  let inc v1 op v2 heap =
    let res =
      match op with
      | OPlus -> value v1 heap + value v2 heap
      | OMinus -> value v1 heap - value v2 heap
    in (Heap.add v1 res heap, free)

  let set v1 v2 heap =
    (Heap.add v1 (value v2 heap) heap, free)

  let test (Cond (v1, v2, k)) heap =
    value v1 heap - value v2 heap > k

  let rec eval = function
    | PSkip -> pay CSkip
    | PSeq (p1, p2) -> pay CSeq1 -$ eval p1 -$ pay CSeq2 -$ eval p2
    | PInc (v1, op, v2) -> pay CSet -$ inc v1 op v2
    | PSet (v1, v2) -> pay CSet -$ set v1 v2
    | PWhile (cond, p) as ploop ->
      guard (test cond)
        (fun () -> pay CWhile1 -$ eval p -$ pay CWhile2 -$ eval ploop)
        (fun () -> pay CWhile3)

  let empty_heap = Heap.empty

  let print_heap =
    Heap.iter (Printf.printf "%s -> %d\n")
end


(* sample metrics *)

module CostFree: METRIC = struct
  type t = int
  type action =
    | CSkip
    | CSet
    | CAssert
    | CWhile1 | CWhile2 | CWhile3
    | CIf1 | CIf2
    | CSeq1 | CSeq2
  let cost _ = 0
  let free = 0
  let concat _ _ = 0
end


(* testing *)

let _ =
  match try Some Sys.argv.(1) with _ -> None with
  | Some "-teval" ->
    let module E = Eval(CostFree) in
    let p = Parse.prog stdin in
    let (hfinal, _) = E.eval p E.empty_heap in
    E.print_heap hfinal
  | _ -> ()
