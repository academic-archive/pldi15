(* under the hood *)

open Parse
open Logic

(*
	0 - no output
	1 - output final annotation
	2 - output final annotation and constraints
*)
let debug = 0

module UidMap = struct
  module M = Map.Make(struct type t = uid let compare = compare end)
  include M
  exception Overwrite
  let add key value map =
    if mem key map then raise Overwrite else
    add key value map
  let findp p = find (prog_id p)
end

module VSet = struct
  include Set.Make(struct type t = var let compare = compare end)
  let of_list = List.fold_left (fun s x -> add x s) empty
  let union = List.fold_left union empty
end


(* first, compute the logical contexts *)
type log = { lpre : ineq list; lpost : ineq list }

let create_logctx =
  let rec f m lpre prog =
    let addpost m id lpost = UidMap.add id { lpre; lpost } m in
    match prog with
    | PSkip id -> addpost m id lpre
    | PAssert (c, id) -> addpost m id (Logic.add (assn_of_cond c) lpre)
    | PInc (x, op, v, id) -> addpost m id (Logic.incr x op v lpre)
    | PSet (x, v, id) -> addpost m id (Logic.set x v lpre)
    | PWhile (c, p, id) ->
      let itr pre = Logic.add (assn_of_cond c) pre in
      let g pre =
        let m' = f m (itr pre) p in
        (m', (UidMap.findp p m').lpost) in
      let m', inv = Logic.fix (itr lpre) g in
      (* Note: we use :: instead of Logic.add here *)
      addpost m' id (assn_negate (assn_of_cond c) :: inv)
    | PIf (c, p1, p2, id) ->
      let a = assn_of_cond c in
      let m = f m (Logic.add a lpre) p1 in
      let m = f m (Logic.add (assn_negate a) lpre) p2 in
      let post1 = (UidMap.findp p1 m).lpost
      and post2 = (UidMap.findp p2 m).lpost
      in addpost m id (Logic.merge post1 post2)
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
  val extra : int -> t
  val compare : t -> t -> int
  val obj : t -> int
  val fold : ('a -> t -> 'a) -> 'a -> VSet.t -> 'a
  val printk : float -> t -> unit
end = struct
  type t = Const | Dst of var * var | Extra of int
  let const = Const
  let dst (u, v) = if u < v then Dst (u, v) else Dst (v, u)
  let extra i = Extra i
  let compare = compare
  let obj = function
    | Dst (VNum a, VNum b) -> abs (a-b) + 10
    | Dst _ -> 10_000
    | _ -> 1
  let fold f a vs =
    let rec pairs a vl =
      match vl with
      | v :: vl ->
        let g a v' = f a (dst (v, v')) in
        pairs (List.fold_left g a vl) vl
      | [] -> a
    in pairs (f a const) (VSet.elements vs)
  let printk k i =
    if abs_float k < 1e-8 then () else
    match i with
    | Const ->
      Printf.printf "%.2f\n" k
    | Dst (v, VNum 0) | Dst (VNum 0, v) ->
      Printf.printf "%.2f |%a|\n" k pp_var v
    | Dst (v1, v2) ->
      Printf.printf "%.2f |%a - %a|\n" k
        pp_var v1 pp_var v2
    | Extra _ -> ()
end

module type CLPSTATE = sig val state : Clp.t end

module Q(C: CLPSTATE) : sig
  type ctx
  val create : VSet.t -> ctx
  val set : ctx -> Idx.t -> (Idx.t * int) list -> int -> ctx
  val eqc : ctx -> ctx -> unit
  val relax : ?kpairs:(int * int) list -> ?xs:id list -> ctx -> ctx
  val merge : ctx list -> ctx
  val free : ctx -> Idx.t -> ctx
  val solve : ctx -> ctx -> unit
end = struct
  module M = Map.Make(Idx)
  type ctx = { cvars : VSet.t; cmap : int M.t }

  let newv ?(neg=false) () =
    let c = [|
      { Clp.column_obj = 0.
      ; Clp.column_lower = if neg then -. max_float else 0.
      ; Clp.column_upper = max_float
      ; Clp.column_elements = [| |]
      } |] in
    Clp.add_columns C.state c;
    Clp.number_columns C.state - 1

  let create cvars =
    let cmap = Idx.fold
      (fun m i -> M.add i (newv ()) m)
      M.empty cvars in
    { cvars; cmap }

  let mkrow ?(lo=0.) ?(up=0.) v' l k =
    let row_elements = Array.of_list begin
      (v', 1.) :: List.map
        (fun (i, w) -> (i, float_of_int (-w))) l
    end in
    if debug > 1 then begin
      let open Printf in
      let c = function
        | (v, w) when w = 1 -> sprintf "v%d" v
        | (v, w) -> sprintf "%d * v%d" w v in
      printf "v%d = %d" v' k;
      List.iter (fun x -> printf " + %s" (c x)) l;
      print_newline ()
    end;
    Clp.add_rows C.state [|
      { Clp.row_lower = float_of_int k +. lo
      ; Clp.row_upper = float_of_int k +. up
      ; row_elements
      } |]

  let set c idx l const =
    let v' = newv () in
    let l = List.map (fun (i, k) -> M.find i c.cmap, k) l in
    mkrow v' l const;
    { c with cmap = M.add idx v' c.cmap }

  let eqc c1 c2 =
    assert (VSet.equal c1.cvars c2.cvars);
    let eqv i =
      if debug > 1 then
        Printf.printf "v%d = v%d\n" (M.find i c1.cmap) (M.find i c2.cmap);
      { Clp.row_lower = 0.; row_upper = 0.
      ; row_elements =
        [| (M.find i c1.cmap, -1.)
         ; (M.find i c2.cmap, 1.) |] } in
    let rows = Array.of_list
      (Idx.fold (fun l i -> eqv i :: l) [] c1.cvars) in
    Clp.add_rows C.state rows

  let relax ?kpairs ?(xs=[]) c =
    let allpairs c =
      let ks = VSet.filter
        (function VNum _ -> true | _ -> false) c.cvars in
      let getk = function VNum k -> k | _ -> assert false in
      let rec f = function
        | n :: l -> List.map (fun x -> (n, x)) l @ f l
        | [] -> [] in
      f (List.map getk (VSet.elements ks)) in
    let kpairs =
      match kpairs with
      | Some l -> l
      | None -> allpairs c in
    let l =
      List.map
        (fun x -> (Idx.dst (VId x, VNum 0), (newv (), -1))) xs @
      List.map
        (fun (n1, n2) ->
          ( Idx.dst (VNum n1, VNum n2)
          , (newv ~neg:true (), - abs (n1-n2))))
        kpairs in
    let c = List.fold_left
      begin fun c (i, (ip, _)) ->
        let v' = newv () in
        mkrow v' [(M.find i c.cmap, 1); (ip, 1)] 0;
        { c with cmap = M.add i v' c.cmap }
      end c l in
    let v' = newv () and ic = Idx.const in
    mkrow v' ((M.find ic c.cmap, 1) :: List.map snd l) 0;
    { c with cmap = M.add ic v' c.cmap }

  let merge cl =
    assert (List.for_all
      (fun {cvars;_} -> VSet.equal cvars (List.hd cl).cvars) cl
    );
    let m (cmap', rows) i =
      let v' = newv () in
      if debug > 1 then
        List.iter (fun {cmap;_} ->
          Printf.printf "v%d >= v%d\n" v' (M.find i cmap)
        ) cl;
      let rec row accu = function
        | {cmap;_} :: cl ->
          let r =
            { Clp.row_lower = -. max_float
            ; Clp.row_upper = 0.
            ; Clp.row_elements = [|(M.find i cmap, 1.); (v', -1.)|]
            }
          in row (r :: accu) cl
        | [] -> accu in
      (M.add i v' cmap', row rows cl) in
    let cvars = (List.hd cl).cvars in
    let cmap, rows = Idx.fold m (M.empty, []) cvars in
    Clp.add_rows C.state (Array.of_list rows);
    {cvars; cmap}

  let free c idx =
    let v' = newv () in
    { c with cmap = M.add idx v' c.cmap }

  let solve cini cfin =
    let obj = Clp.objective_coefficients C.state in
    Idx.fold begin fun () i ->
      let o = float_of_int (Idx.obj i) in
      obj.(M.find i cini.cmap) <- o
    end () cini.cvars;
    Clp.change_objective_coefficients C.state obj;
    flush stdout;
    Clp.set_log_level C.state 0; (* use 0 to turn CLP output off *)
    Clp.initial_solve C.state;   (* initial_solve is good because it uses presolve *)
    let sep () =  print_string "*******\n"; in
    match Clp.status C.state with
    | 0 ->
      let sol = Clp.primal_column_solution C.state in
      let p c = sep (); M.iter (fun i v -> Idx.printk sol.(v) i) c.cmap in
      p cini; if debug > 0 then p cfin
    | _ -> sep(); print_string "LP is INFEASABLE\n"

end


let rec pvars p =
  (* get all variables used in a program *)
  let cvars (Cond (v1, v2, k)) = VSet.of_list [v1; v2; VNum k] in
  match p with
  | PSkip _ -> VSet.empty
  | PAssert (c, _) -> cvars c
  | PSet (id, v2, _) -> VSet.of_list [VId id; v2]
  | PInc (id, _, v, _) -> VSet.of_list [VId id; v]
  | PSeq (p1, p2, _) -> VSet.union [pvars p1; pvars p2]
  | PWhile (c, p, _) -> VSet.union [cvars c; pvars p]
  | PIf (c, p1, p2, _) -> VSet.union [cvars c; pvars p1; pvars p2]

let go lctx cost p =
  (* generate and resolve constraints *)
  let clp_state = Clp.create () in
  let module Q = Q(struct let state = clp_state end) in
  let open Idx in
  let open Eval in
  let vars = VSet.add (VNum 0) (pvars p) in

  let addconst q act = Q.set q const [(const, 1)] (cost act) in
  let rec gen qpost = function

    | PSkip _ -> addconst qpost CSkip

    | PAssert _ -> addconst qpost CAssert

    | PInc (x, op, delta, pid) ->
      let vars = VSet.remove (VId x) vars in
      let {lpre;_} = UidMap.find pid lctx in
      let us = VSet.filter (Logic.entails lpre (VId x) op delta) vars in
      (* relax constant differences *)
      let xs =
        match delta with
        | VNum _ -> []
        | VId y as v ->
          if Logic.entails lpre (VNum 0) OPlus (VNum 1) v
          then [y] else [] in
      let q = Q.relax ~xs qpost in
      (* modify delta's potential *)
      let d0 = Idx.dst (delta, VNum 0) in
      let sum = List.map
        begin fun v ->
          if VSet.mem v us
            then (Idx.dst (VId x, v), -1)
            else (Idx.dst (VId x, v), 1)
        end (VSet.elements vars) in
      let q = Q.set q d0 ((d0, 1) :: sum) 0 in
      (* pay for the assignment *)
      addconst q CSet

    | PSet (x, v, _) ->
      let vars = VSet.remove (VId x) vars in
      let q = qpost in
      (* split potential of |v - u| for all u *)
      let q = VSet.fold begin fun u q ->
          let q =
            if u = v then q else
            Q.set q (Idx.dst (v, u))
              [ (Idx.dst (VId x, u), 1)
              ; (Idx.dst (v, u), 1) ] 0 in
          let q =
            Q.free q (Idx.dst (VId x, u)) in
          q
        end vars q in
      (* pay for the assignment *)
      let q = addconst q CSet in
      (* relax constant differences *)
      Q.relax q

    | PSeq (p1, p2, _) ->
      let qpre2 = gen qpost p2 in
      let qmid = addconst qpre2 CSeq2 in
      let qpre1 = gen (Q.merge [qmid]) p1 in
      let qpre = addconst qpre1 CSeq1 in
      qpre

    | PWhile (_, p, _) ->
      let qinv = addconst qpost CWhile3 in
      let qpost1 = addconst qinv CWhile2 in
      let qpre1 = gen qpost1 p in
      let qinv' = addconst qpre1 CWhile1 in
      Q.eqc qinv qinv';
      qinv'

    | PIf (_, p1, p2, _) ->
      let qpre1 = gen qpost p1 in
      let qpre2 = gen qpost p2 in
      Q.merge [qpre1; qpre2]

    in

  let qpost = Q.create vars in
  let qpre = gen qpost p in
  Q.solve qpre qpost


let _ =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "-tlannot" then
  let p = Parse.pa_prog stdin in
  let l = create_logctx p in
  let pre id =
    let { lpre; lpost } = UidMap.find id l in
    Logic.pp lpre; print_string "\n"
  and post id =
    let { lpre; lpost } = UidMap.find id l in
    print_string "\n"; Logic.pp lpost
  in Parse.pp_prog_hooks pre post p

let _ =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "-tq" then
  let p = Parse.pa_prog stdin in
  let l = create_logctx p in
  go l (function x -> Eval.atomic_ops x) p
