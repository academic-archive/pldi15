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
type pstate = ineq list
type log = { lpre : pstate; lpost : pstate }

let create_logctx =
  let rec f m lpre prog =
    let addpost m id lpost = UidMap.add id { lpre; lpost } m in
    match prog with
    | PSkip id -> addpost m id lpre
    | PBreak id -> addpost m id [assn_false]
    | PAssert (c, id) -> addpost m id (Logic.add (assn_of_cond c) lpre)
    | PInc (x, op, v, id) -> addpost m id (Logic.incr x op v lpre)
    | PSet (x, v, id) -> addpost m id (Logic.set x v lpre)
    | PWhile (c, p, id) ->
      let itr pre = Logic.add (assn_of_cond c) pre in
      let g pre =
        let m' = f m (itr pre) p in
        (m', (UidMap.findp p m').lpost) in
      let m', inv = Logic.fix (itr lpre) g in
      addpost m' id
        (Logic.add (assn_negate (assn_of_cond c))
          (Logic.merge inv lpre))
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
  val compare : t -> t -> int
  val obj : t -> int
  val fold : ('a -> t -> 'a) -> 'a -> VSet.t -> 'a
  val is_const : pstate -> t -> int option
  val printk : float -> t -> unit
end = struct
  type t = Const | Dst of var * var
  let const = Const
  let dst (u, v) = Dst (u, v)
  let compare = compare
  let obj = function
    | Dst (VNum a, VNum b) -> max (b-a) 0 + 10
    | Dst (VNum n, _)
    | Dst (_, VNum n) -> 10_000 + abs n
    | Dst _ -> 10_000
    | _ -> 1
  let fold f a vs =
    let vl = VSet.elements vs in
    let rec pairs a = function
      | v :: tl ->
        let g a v' = if v = v' then a else f a (dst (v, v')) in
        pairs (List.fold_left g a vl) tl
      | [] -> a
    in pairs (f a const) vl
  let is_const l = function
    | Dst (x1, x2) ->
      begin match
        Logic.is_const l x1, Logic.is_const l x2
      with
      | Some k1, Some k2 -> Some (max (k2 - k1) 0)
      | _, _ -> None
      end
    | _ -> None
  let printk k i =
    if abs_float k < 1e-8 then () else
    match i with
    | Const ->
      Printf.printf "%.2f\n" k
    | Dst (v, VNum 0) ->
      Printf.printf "%.2f max(-%a, 0)\n" k pp_var v
    | Dst (VNum 0, v) ->
      Printf.printf "%.2f max(%a, 0)\n" k pp_var v
    | Dst (v1, v2) ->
      Printf.printf "%.2f max(%a - %a, 0)\n" k
        pp_var v2 pp_var v1
end

module Q(C: sig val state : Clp.t end) : sig
  type ctx
  val create : VSet.t -> ctx
  val setl : ctx -> (Idx.t * (Idx.t * int) list * int) list -> ctx
  val set : ctx -> Idx.t -> (Idx.t * int) list -> int -> ctx
  val eqc : ctx -> ctx -> unit
  val relax : pstate -> ?il:Idx.t list -> ctx -> ctx
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

  let setl ({cmap=m;_} as c) eqs =
    let bdgs = List.map
      begin fun (id, l, k) ->
        let v = newv () in
        mkrow v (List.map (fun (i, k) -> M.find i m, k) l) k;
        (id, v)
      end eqs in
    { c with cmap =
      List.fold_left (fun m (i, v) -> M.add i v m) m bdgs }

  let set c id l k = setl c [id, l, k]

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

  let relax ps ?(il=[]) c =
    let ks =
      Idx.fold begin fun a i ->
        match Idx.is_const ps i with
        | Some k -> (i, k) :: a
        | None -> a
      end [] c.cvars in
    let l =
      List.map
        (fun i -> (i, (newv (), -1))) il @
      List.map
        (fun (i, k) -> (i, (newv ~neg:true (), - k))) ks in
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
    { c with cmap = M.add idx (newv ()) c.cmap }

  let solve cini cfin =
    let obj = Clp.objective_coefficients C.state in
    Idx.fold begin fun () i ->
      let o = float_of_int (Idx.obj i) in
      obj.(M.find i cini.cmap) <- o
    end () cini.cvars;
    obj.(M.find Idx.const cfin.cmap) <- -1.;
    Clp.change_objective_coefficients C.state obj;
    flush stdout;
    Clp.set_log_level C.state 0; (* use 0 to turn CLP output off *)
    Clp.initial_solve C.state;
    let sep () =  print_string "*******\n"; in
    match Clp.status C.state with
    | 0 ->
      let sol = Clp.primal_column_solution C.state in
      let () =
        let i = M.find Idx.const cini.cmap in
        sol.(i) <- sol.(i) -. sol.(M.find Idx.const cfin.cmap) in
      let p c = sep (); M.iter (fun i v -> Idx.printk sol.(v) i) c.cmap in
      p cini; if debug > 0 then p cfin
    | _ -> sep(); print_string "Sorry, I could not find a bound.\n"

end


let rec pvars p =
  (* get all variables used in a program *)
  let rec lvars = function
    | LAdd (l1, l2) | LSub (l1, l2) -> VSet.union [lvars l1; lvars l2]
    | LMult (_, l) -> lvars l
    | LVar v -> VSet.of_list [v] in
  let cvars (C (l1, _, l2)) = VSet.union [lvars l1; lvars l2] in
  match p with
  | PSkip _ | PBreak _ -> VSet.empty
  | PAssert (c, _) -> cvars c
  | PSet (id, v2, _) -> VSet.of_list [VId id; v2]
  | PInc (id, _, v, _) -> VSet.of_list [VId id; v]
  | PSeq (p1, p2, _) -> VSet.union [pvars p1; pvars p2]
  | PWhile (c, p, _) -> VSet.union [cvars c; pvars p]
  | PIf (c, p1, p2, _) -> VSet.union [cvars c; pvars p1; pvars p2]

let go lctx cost p =
  (* generate and resolve constraints *)
  let module Q = Q(struct let state = Clp.create () end) in
  let open Idx in
  let open Eval in
  let vars = VSet.add (VNum 0) (pvars p) in

  let addconst q act = Q.set q const [(const, 1)] (cost act) in
  let rec gen_ qbrk qseq =
    let gen = gen_ qbrk in function

    | PSkip _ -> addconst qseq CSkip

    | PAssert _ -> addconst qseq CAssert

    | PBreak _ -> addconst (Q.merge [qbrk]) CBreak

    | PInc (x, op, y, pid) ->
      let vars = VSet.remove (VId x) vars in
      let {lpre; lpost} = UidMap.find pid lctx in
      let z = LVar (VNum 0) in
      let eqs, rlx =
        let opy, iopyz, izopy =
          let iyz = Idx.dst (y, VNum 0) in
          let izy = Idx.dst (VNum 0, y) in
          match op with
          | OPlus -> LVar y, iyz, izy
          | OMinus -> LMult (-1, LVar y), izy, iyz in
        let xopy = LAdd (LVar (VId x), opy) in
        let sum opy invx inxv = VSet.fold
          begin fun v sum ->
            if invx v then (Idx.dst (v, VId x), -1) :: sum else
            if inxv v then (Idx.dst (VId x, v), -1) :: sum else
            if opy > 0 then (Idx.dst (v, VId x), 1) :: sum else
            if opy < 0 then (Idx.dst (VId x, v), 1) :: sum else
            failwith "bug in increment rule"
          end vars [] in
        match
          Logic.entails lpre opy CLe z,
          Logic.entails lpre opy CGe z
        with
        | true, true -> [], []
        | false, false ->
          let f _ = false
          in [iopyz, sum (-1) f f; izopy, sum (+1) f f], []
        | true, false -> (* op y <= 0 *)
          let r = Logic.entails lpre opy CLt z in
          let sum = sum (-1)
            (fun v -> Logic.entails lpre xopy CGe (LVar v))
            (fun _ -> false)
          in [iopyz, sum], if r then [iopyz] else []
        | false, true -> (* op y >= 0 *)
          let r = Logic.entails lpre opy CGt z in
          let sum = sum (+1)
            (fun _ -> false)
            (fun v -> Logic.entails lpre xopy CLe (LVar v))
          in [izopy, sum], if r then [izopy] else []
      in
      if eqs = [] && Logic.entails lpre z CLt z then qseq else
      (* relax constant indices and y if necessary *)
      let q = Q.relax lpost ~il:rlx qseq in
      (* transfer potential to +y or -y *)
      let q = Q.setl q (List.map (fun (i,s) -> i,(i,1)::s,0) eqs) in
      (* pay for the assignment *)
      addconst q CSet

    | PSet (x, v, pid) ->
      let vars = VSet.remove (VId x) vars in
      let q = qseq in
      (* split potential of [v, u] and [u, v] for all u *)
      let q = VSet.fold begin fun u q ->
          let q =
            if u = v then q else
            let q = Q.set q (Idx.dst (v, u))
                [ (Idx.dst (VId x, u), 1)
                ; (Idx.dst (v, u), 1) ] 0 in
            let q = Q.set q (Idx.dst (u, v))
                [ (Idx.dst (u, VId x), 1)
                ; (Idx.dst (u, v), 1) ] 0 in
            q in
          Q.free (Q.free q (Idx.dst (u, VId x))) (Idx.dst (VId x, u))
        end vars q in
      (* pay for the assignment *)
      let q = addconst q CSet in
      (* relax constant differences *)
      Q.relax (UidMap.find pid lctx).lpre q

    | PSeq (p1, p2, _) ->
      let qpre2 = gen qseq p2 in
      let qmid = addconst qpre2 CSeq2 in
      let qpre1 = gen (Q.merge [qmid]) p1 in
      let qpre = addconst qpre1 CSeq1 in
      qpre

    | PWhile (_, p, _) ->
      let qinv = Q.merge [addconst qseq CWhile3] in
      let qseq1 = addconst qinv CWhile2 in
      let qpre1 = gen_ qseq qseq1 p in
      let qinv' = addconst qpre1 CWhile1 in
      Q.eqc qinv qinv';
      qinv'

    | PIf (_, p1, p2, _) ->
      let qpre1 = addconst (gen qseq p1) CIf1 in
      let qpre2 = addconst (gen qseq p2) CIf2 in
      Q.merge [qpre1; qpre2]

    in

  let q = Q.create vars in
  let qpre = gen_ q q p in
  Q.solve qpre q


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
