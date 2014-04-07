(* under the hood *)

open Parse
open Logic

module UidMap = struct
  module M = Map.Make(struct type t = uid  let compare = compare end)
  include M
  exception Overwrite
  let add key value map =
    if mem key map then raise Overwrite else
    add key value map
  let findp p = find (prog_id p)
end

(* first, compute the logical contexts *)
type log = { lpre : aps; lpost : aps }

let create_logctx =
  let rec f m lpre prog =
    let addpost m id lpost = UidMap.add id { lpre; lpost } m in
    match prog with
    | PSkip id -> addpost m id lpre
    | PAssert (c, id) -> addpost m id (aps_add (assn_of_cond c) lpre)
    | PInc (x, op, v, id) -> addpost m id (aps_incr x op v lpre)
    | PSet (x, v, id) -> addpost m id (aps_set x v lpre)
    | PWhile (c, p, id) ->
      let itr pre = aps_add (assn_of_cond c) pre in
      let g pre =
        let m' = f m (itr pre) p in
        (m', (UidMap.findp p m').lpost) in
      let m', inv = aps_fix (itr lpre) g in
      (* Note: we use :: instead of aps_add here *)
      addpost m' id (assn_negate (assn_of_cond c) :: inv)
    | PSeq (p1, p2, id) ->
      let m1 = f m lpre p1 in
      let m2 = f m1 (UidMap.findp p1 m1).lpost p2 in
      addpost m2 id (UidMap.findp p2 m2).lpost
  in f UidMap.empty []


(* second, generate linear programming problem *)
module Idx : sig
  type t
  val const : t
  val dst : var * var -> t
  (* val extra : int -> t *)
  val compare : t -> t -> int
  val fold : ('a -> t -> 'a) -> 'a -> var list -> 'a
end = struct
  type t = Const | Dst of var * var | Extra of int
  let const = Const
  let dst (u, v) = if u < v then Dst (u, v) else Dst (v, u)
  let extra i = Extra i
  let compare = compare
  let fold f a vl =
    let rec pairs a vl =
      match vl with
      | v :: vl ->
        let g a v' = f a (dst (v, v')) in
        pairs (List.fold_left g a vl) vl
      | [] -> a
    in pairs (f a const) vl
end

module type CLPSTATE = sig
  val state : Clp.t
  val next_var : int ref
end

module Q(C: CLPSTATE) : sig
  type ctx
  val create : var list -> ctx
  val set : ctx -> Idx.t -> (Idx.t * int) list -> int -> ctx
  val solve : ctx -> unit
end = struct
  module S = Set.Make(struct
    type t = var
    let compare = compare
  end)
  module M = Map.Make(Idx)
  type ctx = { cvars : S.t; cmap : int M.t }

  let newv () =
    let rows = Clp.number_rows C.state in
    let cols = Clp.number_columns C.state in
    Clp.resize C.state rows (cols + 1);
    let v = !C.next_var in
    incr C.next_var; v

  let create vl =
    let cvars = List.fold_left
      (fun s v -> S.add v s)
      S.empty vl in
    let cmap = Idx.fold
      (fun m i -> M.add i (newv ()) m)
      M.empty (S.elements cvars) in
    { cvars; cmap }

  let set c idx l const =
    let v' = newv () in
    let row_elements = Array.of_list begin
      (v', -1.) :: List.map
        (fun (i, w) -> ((M.find i c.cmap), float_of_int w)) l
    end in
    let k = float_of_int (-const) in
    Clp.add_rows C.state [|
      { Clp.row_lower = k
      ; Clp.row_upper = k
      ; row_elements }
    |];
    { cvars = c.cvars; cmap = M.add idx v' c.cmap }

  let solve c =
    let obj = Clp.objective_coefficients C.state in
    Idx.fold (fun () i -> obj.(M.find i c.cmap) <- 1.) ()
      (S.elements c.cvars);
    Clp.change_objective_coefficients C.state obj;
    Clp.primal C.state

end


let rec pvars p =
  (* get all variables used in a program (with duplicates) *)
  let cvars (Cond (v1, v2, _)) = [v1; v2] in
  match p with
  | PSkip _ -> []
  | PAssert (c, _) -> cvars c
  | PSet (id, v2, _) -> [VId id; v2]
  | PInc (id, _, v, _) -> [VId id; v]
  | PSeq (p1, p2, _) -> pvars p1 @ pvars p2
  | PWhile (c, p, _) -> cvars c @ pvars p

let go cost p =
  (* generate and resolve constraints *)
  let clp_state = Clp.create () in
  let module Q = Q(struct
    let state = clp_state
    let next_var = ref 0
  end) in
  let open Idx in
  let open Eval in

  let rec gen qpost = function
    | PSkip _ -> Q.set qpost const [(const, 1)] (cost CSkip)
    | PAssert _ -> Q.set qpost const [(const, 1)] (cost CAssert)
    | PSeq (p1, p2, _) ->
      let qpre1 = gen qpost p1 in
      let qmid = Q.set qpre1 const [(const, 1)] (cost CSeq2) in
      let qpre2 = gen qmid p2 in
      let qpre = Q.set qpre2 const [(const, 1)] (cost CSeq1) in
      qpre
    | _ -> failwith "not implemented (gen)" in

  let qpre = gen (Q.create (VNum 0 :: pvars p)) p in
  Q.solve qpre


let _ =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "-tlannot" then
  let p = Parse.pa_prog stdin in
  let l = create_logctx p in
  let pre id =
    let { lpre; lpost } = UidMap.find id l in
    Logic.pp_aps lpre; print_string "\n"
  and post id =
    let { lpre; lpost } = UidMap.find id l in
    print_string "\n"; Logic.pp_aps lpost
  in Parse.pp_prog_hooks pre post p

let _ =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "-tq" then
  let p = Parse.pa_prog stdin in
  (* let l = create_logctx p in *)
  go (function x -> Eval.atomic_ops x) p
