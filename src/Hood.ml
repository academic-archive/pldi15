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
  val compare : t -> t -> int
  val fold : ('a -> t -> 'a) -> 'a -> var list -> 'a
end = struct
  type t = Const | Dst of var * var
  let const = Const
  let dst (u, v) = if u < v then Dst (u, v) else Dst (v, u)
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
  type ineq = Eq | Le
  val create : var list -> ctx
end = struct
  module M = Map.Make(Idx)
  type ctx = { cvars : var list; cmap : int M.t }
  let newv () =
    let v = !C.next_var in
    let rows = Clp.number_rows C.state in
    let cols = Clp.number_columns C.state in
    Clp.resize C.state rows (cols + 1);
    incr C.next_var;
    v
  let create vl =
    { cvars = vl
    ; cmap = Idx.fold
        (fun m i -> M.add i (newv ()) m)
        M.empty vl
    }
  type ineq = Eq | Le
end


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
