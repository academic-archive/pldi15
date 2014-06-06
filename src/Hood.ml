(* under the hood *)

open Parse
open Logic
open Tools

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


(* compute the logical states *)
type pstate = ineq list
type lannot = { lpre: pstate; lpost: pstate }

let create_logctx =
  let rec f m brk lpre prog =
    let addpost m id lpost = UidMap.add id { lpre; lpost } m in
    match prog with
    | PTick (_, id) -> addpost m id lpre
    | PBreak id -> brk := lpre :: !brk; addpost m id bottom
    | PAssert (c, id) -> addpost m id (Logic.conj (of_cond c) lpre)
    | PReturn (_, id) -> addpost m id bottom
    | PCall (_, _, _, id) -> addpost m id []
    | PInc (x, op, v, id) -> addpost m id (Logic.incr x op v lpre)
    | PSet (x, vo, id) -> addpost m id (Logic.set x vo lpre)
    | PWhile (c, p, id) ->
      let itr pre = Logic.conj (of_cond c) pre in
      let out pre = Logic.conj (of_cond (cond_neg c)) pre in
      let g pre =
        let brk = ref [] in
        let m' = f m brk (itr pre) p in
        let post = (UidMap.findp p m').lpost in
        ((m', out post :: !brk), post) in
      let (m', brk), inv = Logic.fix (itr lpre) g in
      addpost m' id (List.fold_left Logic.merge (out lpre) brk)
    | PIf (c, p1, p2, id) ->
      let m = f m brk (Logic.conj (of_cond c) lpre) p1 in
      let m = f m brk (Logic.conj (of_cond (cond_neg c)) lpre) p2 in
      let post1 = (UidMap.findp p1 m).lpost
      and post2 = (UidMap.findp p2 m).lpost
      in addpost m id (Logic.merge post1 post2)
    | PSeq (p1, p2, id) ->
      let m1 = f m brk lpre p1 in
      let m2 = f m1 brk (UidMap.findp p1 m1).lpost p2 in
      addpost m2 id (UidMap.findp p2 m2).lpost
  in let g m {fbody;_} = f m (ref []) [] fbody
  in fun (fl, p) ->
    List.fold_left g (f UidMap.empty (ref []) [] p) fl


(* indices we use to name lp variables *)
module Idx : sig
  type t
  val compare: t -> t -> int
  val const: t
  val dst: var * var -> t
  val map: (var -> var) -> t -> t option
  val obj: t -> int
  val fold: ('a -> t -> 'a) -> 'a -> VSet.t -> 'a
  val value: pstate -> t -> int option
  val printk: float -> t -> unit
end = struct
  type t = Const | Dst of var * var
  let compare = compare
  let const = Const
  let dst (u, v) = assert (u <> v); Dst (u, v)
  let map f = function
    | Const -> Some Const
    | Dst (a, b) ->
      let a' = f a and b' = f b in
      if a' = b' then None else
      Some (Dst (a', b'))
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
  let value l = function
    | Dst (x1, x2) ->
      begin match
        Logic.value l x1, Logic.value l x2
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

(* quantitative contexts and their operations *)
module Q(C: sig val state: Clp.t end): sig
  type ctx
  val vars: ctx -> VSet.t
  val empty: ctx
  val addv: ctx -> VSet.t -> ctx
  val delv: ctx -> ?zero: bool -> VSet.t -> ctx
  val setl: ctx -> (Idx.t * (Idx.t * int) list * int) list -> ctx
  val set: ctx -> Idx.t -> (Idx.t * int) list -> int -> ctx
  val zero: ctx -> Idx.t -> ctx
  val eqc: ctx -> ctx -> unit
  val relax: pstate -> ?il:Idx.t list -> ctx -> ctx
  val merge: ctx list -> ctx
  val free: ctx -> Idx.t -> ctx
  val lift: ctx -> ctx -> ctx
  val subst: ctx -> id list -> var list -> ctx
  val solve: ctx -> ctx -> unit
end = struct
  module M = Map.Make(Idx)
  type ctx = { cvars: VSet.t; cmap: int M.t }

  let newv ?(neg=false) () =
    let c = [|
      { Clp.column_obj = 0.
      ; Clp.column_lower = if neg then -. max_float else 0.
      ; Clp.column_upper = max_float
      ; Clp.column_elements = [| |]
      } |] in
    Clp.add_columns C.state c;
    Clp.number_columns C.state - 1

  let vars c = c.cvars

  let empty = {cvars = VSet.empty; cmap = M.empty}

  let addv c vs =
    assert (VSet.is_empty (VSet.inter (vars c) vs));
    let cvars = VSet.union [vars c; vs] in
    let cmap = Idx.fold
      (fun m i ->
        let v =
          try M.find i c.cmap with
          Not_found -> newv () in
        M.add i v m)
      M.empty cvars in
    {cvars; cmap}

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

  let zero c id = mkrow (M.find id c.cmap) [] 0; c

  let delv c ?(zero=true) vs =
    assert (VSet.subset vs (vars c));
    let cvars = VSet.diff (vars c) vs in
    let m _ vo vo' =
      match vo, vo' with
      | Some _, Some _ -> vo
      | Some v, None -> if zero then mkrow v [] 0; None
      | _, _ -> assert false in
    let c' = Idx.fold (fun m i -> M.add i 0 m) M.empty cvars in
    {cvars; cmap = M.merge m c.cmap c'}

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
        match Idx.value ps i with
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

  let lift q q' =
    (* assert (VSet.subset (vars q) (vars q')); *)
    addv q (VSet.diff (vars q') (vars q))

  let subst {cvars; cmap} xl vl =
    let rename =
      let h = Hashtbl.create 11 in
      List.iter2 (Hashtbl.add h) xl vl;
      function
      | VId id as v ->
        (try Hashtbl.find h id with Not_found -> v)
      | VNum _ as v -> v in
    let h = Hashtbl.create 257 in
    Idx.fold (fun () i ->
      match Idx.map rename i with
      | Some i' -> Hashtbl.add h i' i
      | None -> ()
    ) () cvars;
    let cmap = Idx.fold (fun m i ->
        match Hashtbl.find_all h i with
        | [] -> M.add i (newv ()) m
        | [i'] -> M.add i (M.find i' cmap) m
        | payfor ->
          let v = newv () in
          mkrow v (List.map (fun i -> (M.find i cmap,1)) payfor) 0;
          M.add i v m
      ) M.empty cvars in
    {cvars; cmap}

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
      let p c = sep ();
        Idx.fold (fun () i -> Idx.printk sol.(M.find i c.cmap) i)
          () (vars c) in
      p cini; if debug > 0 then p cfin
    | _ -> sep(); print_string "Sorry, I could not find a bound.\n"

end


let analyze lctx cost (fdefs, p) =
  (* generate and resolve constraints *)
  let module Q = Q(struct let state = Clp.create () end) in
  let open Idx in
  let open Eval in

  let addconst q act = Q.set q const [(const, 1)] (cost act) in
  let rec gen_ qfuncs qret qbrk qseq =
    let gen = gen_ qfuncs qret qbrk in function

    | PTick (n, _) -> addconst qseq (CTick n)
    | PAssert _ -> addconst qseq CAssert
    | PBreak _ -> addconst qbrk CBreak
    | PReturn (v, _) ->
      let q = Q.lift qret qseq in
      Q.delv (Q.subst q ["%ret"] [v])
        ~zero:false (VSet.singleton (VId "%ret"))

    | PCall (ret, fname, args, _) ->
      let f = List.find (fun x -> x.fname = fname) fdefs in
      let fargs = VSet.of_list (List.map (fun x -> VId x) f.fargs) in
      let flocs = VSet.of_list (List.map (fun x -> VId x) f.flocs) in

      let qret = Q.addv qseq (VSet.singleton (VId "%ret")) in
      let qret =
        match ret with
        | Some x -> Q.subst qret [x] [VId "%ret"]
        | None -> qret in

      begin match
        try Some (List.assoc fname qfuncs)
        with Not_found -> None
      with

      | None -> (* unfold case *)
        let qcall = Q.addv Q.empty (VSet.union [fargs; Q.vars qseq]) in
        let qfun = Q.delv qret ~zero:false (VSet.singleton (VId "%ret")) in
        let qfun = Q.addv qfun (VSet.union [fargs; flocs]) in
        let qbdy = gen_
          ((fname, (qcall, qret)) :: qfuncs)
          qret Q.empty qfun f.fbody in
        let qcall' = Q.delv qbdy flocs in
        Q.eqc qcall qcall';
        let q = Q.subst qcall f.fargs args in
        Q.delv q ~zero:false fargs

      | Some (qcallf, qretf) -> (* recursive case *)
        let vdiff = VSet.diff (Q.vars qseq) (Q.vars qretf) in
        let qretf = Q.addv qretf vdiff in
        let _ = Q.delv qretf vdiff in
        Q.eqc qret qretf;
        Q.subst (Q.lift qcallf qseq) f.fargs args

      end

    | PInc (x, op, y, pid) ->
      let vars = VSet.remove (VId x) (Q.vars qseq) in
      let {lpre; lpost} = UidMap.find pid lctx in
      let z = LVar (VNum 0) in
      let eqs, rlx =
        let opy, iopyz, izopy =
          let iyz = dst (y, VNum 0) and izy = dst (VNum 0, y) in
          match op with
          | OPlus -> LVar y, iyz, izy
          | OMinus -> LMult (-1, LVar y), izy, iyz in
        let xopy = LAdd (LVar (VId x), opy) in
        let sum opy invx inxv = VSet.fold
          begin fun v sum ->
            if invx v then (dst (v, VId x), -1) :: sum else
            if inxv v then (dst (VId x, v), -1) :: sum else
            if opy > 0 then (dst (v, VId x), 1) :: sum else
            if opy < 0 then (dst (VId x, v), 1) :: sum else
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

    | PSet (x, Some v, pid) ->
      let q = addconst (Q.subst qseq [x] [v]) CSet in
      (* relax constant differences *)
      Q.relax (UidMap.find pid lctx).lpre q

      (*
      let vars = VSet.remove (VId x) (Q.vars qseq) in
      let q = qseq in
      if v = VId x then addconst q CSet else
      (* split potential of [v, u] and [u, v] for all u *)
      let q = VSet.fold begin fun u q ->
          let q =
            if u = v then q else
            let q = Q.set q (dst (v, u))
              [(dst (VId x, u), 1); (dst (v, u), 1)] 0 in
            let q = Q.set q (dst (u, v))
              [(dst (u, VId x), 1); (dst (u, v), 1)] 0 in
            q in
          Q.free (Q.free q (dst (u, VId x))) (dst (VId x, u))
        end vars q in
      (* pay for the assignment *)
      let q = addconst q CSet in
      (* relax constant differences *)
      Q.relax (UidMap.find pid lctx).lpre q
      *)

    | PSet (x, None, _) ->
      let vars = VSet.remove (VId x) (Q.vars qseq) in
      let q = VSet.fold begin fun u q ->
          let q = Q.zero q (dst (VId x, u)) in
          let q = Q.zero q (dst (u, VId x)) in
          Q.free (Q.free q (dst (u, VId x))) (dst (VId x, u))
        end vars qseq in
      (* pay for the assignment *)
      addconst q CSet

    | PSeq (p1, p2, _) ->
      let qpre2 = gen qseq p2 in
      let qmid = addconst qpre2 CSeq2 in
      let qpre1 = gen (Q.merge [qmid]) p1 in
      let qpre = addconst qpre1 CSeq1 in
      qpre

    | PWhile (_, p, _) ->
      let qinv = Q.merge [addconst qseq CWhile3] in
      let qseq1 = addconst qinv CWhile2 in
      let qpre1 = gen_ qfuncs qret qseq qseq1 p in
      let qinv' = addconst qpre1 CWhile1 in
      Q.eqc qinv qinv';
      qinv'

    | PIf (_, p1, p2, _) ->
      let qpre1 = addconst (gen qseq p1) CIf1 in
      let qpre2 = addconst (gen qseq p2) CIf2 in
      Q.merge [qpre1; qpre2]

    in

  let q = Q.addv Q.empty
    (VSet.add (VNum 0) (file_globals (fdefs, p))) in
  let qret = Q.addv q (VSet.singleton (VId "%ret")) in
  let qpre = gen_ [] qret Q.empty q p in
  Q.solve qpre q


let _ =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "-tlannot" then
  let f = Parse.pa_file stdin in
  let l = create_logctx f in
  let pre id =
    let { lpre; lpost } = UidMap.find id l in
    Logic.pp lpre; print_string "\n"
  and post id =
    let { lpre; lpost } = UidMap.find id l in
    print_string "\n"; Logic.pp lpost
  in Parse.pp_file_hooks pre post f

let _ =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "-tq" then
  let f = Tools.clean_file (Parse.pa_file stdin) in
  analyze (create_logctx f) Eval.atomic_metric f
