(* evaluation *)
type action =
  | CTick of int
  | CBreak
  | CAssert
  | CSet
  | CWhile1 | CWhile2 | CWhile3
  | CIf1 | CIf2
  | CSeq1 | CSeq2

let atomic_ops = function
  | CTick 0 | CSet | CAssert -> 1
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
  type result = OSeq of heap | OBreak of heap

  let (-$) c1 c2 heap =
    match c1 heap with
    | (OSeq heap1, cost1) ->
      let (res2, cost2) = c2 heap1 in
      (res2, concat cost1 cost2)
    | (OBreak _, _) as x -> x

  let pay price heap = (OSeq heap, lift price)

  let guard f c1 c2 heap =
    if f heap then c1 () heap else c2 () heap

  let break heap = (OBreak heap, zero)

  let catch c heap =
    match c heap with
    | (OBreak heap, cost) -> (OSeq heap, cost)
    | (OSeq _, _) as x -> x

  let value v h =
    match v with
    | VNum n -> n
    | VId id -> try Heap.find id h with Not_found -> 0

  let inc id op v heap =
    let res =
      match op with
      | OPlus -> value (VId id) heap + value v heap
      | OMinus -> value (VId id) heap - value v heap
    in (OSeq (Heap.add id res heap), zero)

  let set id v heap =
    (OSeq (Heap.add id (value v heap) heap), zero)

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
      | PTick (n, _) -> pay (CTick n)
      | PBreak _ -> pay CBreak -$ break
      | PSeq (p1, p2, _) -> pay CSeq1 -$ eval p1 -$ pay CSeq2 -$ eval p2
      | PInc (v1, op, v2, _) -> pay CSet -$ inc v1 op v2
      | PSet (v1, v2, _) -> pay CSet -$ set v1 v2
      | PWhile (cond, p, _) as ploop ->
	catch begin
          guard (test cond)
            (fun () -> pay CWhile1 -$ eval p -$ pay CWhile2 -$ eval ploop)
            (fun () -> pay CWhile3)
	end
      | PAssert (c, _) as p ->
        guard (test c)
          (fun () -> pay CAssert)
          (fun () -> raise (ProgramFailure p))
      | PIf (c, p1, p2, _) ->
        guard (test c)
          (fun () -> pay CIf1 -$ eval p1)
          (fun () -> pay CIf2 -$ eval p2)
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
      let (res, cost) = E.eval atomic_ops p E.empty_heap in
      let hfinal = match res with E.OSeq h | E.OBreak h -> h in
      E.print_heap hfinal;
      Printf.printf "evaluation cost: %d\n" cost
    with E.ProgramFailure p ->
      Printf.printf "program failure on: "; Parse.pp_prog p;
      exit 1
    end
  | _ -> ()
