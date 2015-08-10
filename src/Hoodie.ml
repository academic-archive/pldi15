(* analysis for the cfg *)

open Ast
open Tools

(*
	0 - no output
	1 - output final annotation
	2 - output final annotation and constraints
	4 - print sign of variables (ugly)
*)
let debug = 0

type pstate = Logic.ineq list

(* bye bye, I'll inline you with the analysis
 * kept here for future reference

(* compute the logical states *)
type lannot = { lpre: pstate; lpost: pstate }

let lannot =
  let open Logic in
  let rec f' locs brk lpre prog =
    let f = f' locs in
    let post lpost = {lpre; lpost} in
    match prog with
    | PTick (n, _) -> PTick (n, post lpre)
    | PBreak _ -> brk := lpre :: !brk; PBreak (post bottom)
    | PAssert (c, _) -> PAssert (c, post ((of_cond c) @ lpre))
    | PReturn (v, _) -> PReturn (v, post bottom)
    | PCall (ret, f, args, _) ->
      let locs = match ret with
        | None -> locs
        | Some x -> List.filter ((<>) x) locs in
      PCall (ret, f, args, post (Logic.call locs lpre))
    | PInc (x, op, v, _) -> PInc (x, op, v, post (Logic.incr x op v lpre))
    | PSet (x, vo, id) -> PSet (x, vo, post (Logic.set x vo lpre))
    | PLoop (bdy, _) ->
      let g ps =
        let brk = ref [] in
        let bdy' = f brk ps bdy in
        let post = (prog_data bdy').lpost in
        ((bdy', !brk), post) in
      let (bdy, brk), _ = Logic.fix lpre g in
      PLoop (bdy, post (List.fold_left Logic.merge bottom brk))
    | PIf (c, p1, p2, _) ->
      let p1 = f brk (Logic.conj (of_cond c) lpre) p1 in
      let p2 = f brk (Logic.conj (of_cond (cond_neg c)) lpre) p2 in
      let post1 = (prog_data p1).lpost
      and post2 = (prog_data p2).lpost
      in PIf (c, p1, p2, post (Logic.merge post1 post2))
    | PSeq (p1, p2, _) ->
      let p1 = f brk lpre p1 in
      let p2 = f brk (prog_data p1).lpost p2 in
      PSeq (p1, p2, post (prog_data p2).lpost)
  in let g ({fbody;fargs;flocs;_} as f) =
    { f with fbody = f' (fargs@flocs) (ref []) [] fbody }
  in fun (fl, p) ->
    List.map g fl, f' [] (ref []) [] p
*)

(* indices we use to name lp variables *)
module Idx : sig
  type t
  type delta
  val compare: t -> t -> int
  val eq: t -> t -> bool
  val deg: t -> int
  val one: t
  val dst: var * var -> t
  val map: (var -> var) -> t -> t option
  val local: VSet.t -> t -> bool
  val obj: t -> int
  val fold: ('a -> t -> 'a) -> 'a -> VSet.t -> 'a
  val range: pstate -> t -> ((int * t) * (int * t))
  val print: t -> unit
  val printk: float -> t -> unit
  val print_delta: delta -> unit
  module DMap: Map.S with type key = delta
  val expand: int -> var * var -> t -> int DMap.t list
  val shift: VSet.t -> var -> int -> t -> int DMap.t
end = struct
  type base = Dst of var * var
  module I = struct
    include Map.Make (struct
      type t = base
      let compare = compare
    end)
    type indice = int t
    let k b i = try find b i with Not_found -> 0
    let deg i = fold (fun _ -> (+)) i 0
    let add k v m =
      if v <> 0 then add k v m else
      if mem k m then remove k m else m
    let mult =
      let a _ x y =
        let f = function Some n -> n | None -> 0 in
        let z = f x + f y in
        if z = 0 then None else Some z in
      merge a
  end
  type t = I.indice

  let polycmp = compare (* Save Pervasives' compare. *)
  let compare = I.compare compare
  let eq i j = compare i j = 0
  let deg i = I.deg i

  let one = I.empty
  let dst (u, v) = I.add (Dst (u, v)) 1 one
  let invalid i =
    (* let num = function VNum _ -> true | _ -> false in *)
    let f (Dst (a,b)) _ =
      a=b (* || (num a && num b) *) in
    I.exists f i

  let map f i =
    let g (Dst (a, b)) = Dst (f a, f b) in
    let i' =
      I.fold (fun b k i' ->
        I.mult i' (I.add (g b) k one)
      ) i one in
    if invalid i' then None else Some i'

  let local vs i =
    let f = function
      | Dst (VNum _, a) | Dst (a, VNum _) -> VSet.mem a vs
      | Dst (a, b) -> VSet.mem a vs && VSet.mem b vs in
    if I.deg i = 0 then false else
    I.for_all (fun b _ -> f b) i

  let rec pow a b = if b = 0 then 1 else a * pow a (b-1)
  let obj i =
    let f = function
      | Dst (VNum a, VNum b) -> max (b-a) 0 + 100
      | Dst (VNum n, _) -> 10000 - abs n
      | Dst (_, VNum n) -> 10000 + abs n
      | Dst _ -> 10000 in
    I.fold (fun b k o -> o * pow (f b) k) i 1
  let print =
    let f b k = match b with
      | Dst (v1, v2) ->
        Printf.printf " |[%a, %a]|"
          Parse.pp_var v1 Parse.pp_var v2;
        if k <> 1 then Printf.printf "^%d" k in
    I.iter f
  let printk k i =
    if abs_float k < 1e-6 then () else begin
      Printf.printf "%.2f" k; print i; print_newline ()
    end

  let range l i =
    let loh = Hashtbl.create 101 in
    let hih = Hashtbl.create 101 in
    let irng = let memo = Hashtbl.create 101 in
      fun x1 x2 ->
        try Hashtbl.find memo (x1,x2) with Not_found ->
        let r = Logic.irange l x1 x2 in
        Hashtbl.add memo (x1,x2) r; r in
    let f (Dst (x1, x2) as d) k (rl, ru) =
      let z =
        match x1, x2 with
        | VId v, VNum n ->
          Hashtbl.add hih v n;
          (try Hashtbl.find loh v >= n - 1
           with Not_found -> false)
        | VNum n, VId v ->
          Hashtbl.add loh v n;
          (try n >= Hashtbl.find hih v - 1
           with Not_found -> false)
        | _ -> false in
      if z then ((0, one), (0, one)) else
      let (l, u) = irng x1 x2 in
      let f = function
        | (None, (b, i)) -> (b, I.add d k i)
        | (Some a, (b, i)) -> (pow a k * b, i) in
      (f (l, rl), f (u, ru)) in
    I.fold f i ((1, one), (1, one))

  let fold deg f a vars =
    let vl = VSet.elements vars in
    let rec pairs a h = function
      | v :: tl ->
        let g a v' = h a (dst (v,v')) in
        pairs (List.fold_left g a vl) h tl
      | [] -> a in
    let plist = pairs [] (fun l a -> a::l) vl in
    let rec iota b a d l =
      if invalid b then a else
      let a = f a b in
      if d = deg || l = [] then a else
      let rec f a = function
        | p :: l ->
          f (iota (I.mult b p) a (d+1) (p::l)) l
        | [] -> a in
      f a l in
    iota one a 0 plist

  (* DEBUG fold *)
  let _ =
    let deg = 2 in
    let vars = VSet.of_list
      [ VId "a"; VId "b"; VNum 2; VNum 0 ] in
    if false then
    fold deg (fun () i ->
      print_string "1";
      print i;
      print_newline ()
    ) () vars
  (* END DEBUG *)

  let fold f a vars = fold 2 f a vars

  (* Extended indices (with products of deltas). *)
  type delta = {deltas: (int * int) array; base: t}
  module DMap = Map.Make(struct
    type t = delta
    let compare di1 di2 =
      let c = Pervasives.compare di1.deltas di2.deltas in
      if c = 0 then compare di1.base di2.base else c
  end)
  let print_delta {deltas; base} =
    for i = 0 to Array.length deltas - 1 do
      let p s n k =
        if k = 0 then () else begin
          Printf.printf " %s%d" s n;
          if k <> 1 then
          Printf.printf "^%d" k;
        end in
      let (l,r) = deltas.(i) in
      p "l" i l;
      p "r" i r;
    done; print base

  let expand nvs =
    let maxdeg = 5 in
    let dummy = Dst (VNum 0, VId "X") in
    let memo = Array.make maxdeg [] in
    let fill deg =
      let mult v {deltas; base} n m =
        let k i m = try DMap.find i m with Not_found -> 0 in
        if v = nvs then
          let i =
            { deltas
            ; base = I.add dummy (1 + I.k dummy base) base
            } in
          DMap.add i (n + k i m) m
        else
          let (a, b) = deltas.(v) in
          let d = Array.copy deltas in
          let i = d.(v) <- (a+1, b); {deltas=d; base} in
          let m = DMap.add i (n + k i m) m in
          let d = Array.copy deltas in
          let i = d.(v) <- (a, b+1); {deltas=d; base} in
          DMap.add i (n + k i m) m in
      if deg = 0 then
        let i = {deltas=Array.make nvs (0,0); base=one} in
        [ DMap.singleton i 1 ]
      else begin
        memo.(deg-1) |>
        List.fold_left (fun l m ->
          let rec loop v =
            if v > nvs then l else
            DMap.fold (mult v) m DMap.empty :: loop (v+1) in
          loop 0
        ) [] |>
        List.sort_uniq (DMap.compare polycmp)
      end in
    for deg = 0 to maxdeg - 1 do memo.(deg) <- fill deg done;
    (* DEBUG expand *)
    let p m =
      Printf.printf "0";
      DMap.iter (fun i n ->
        if n <> 0 then
        Printf.printf " + %d" n; print_delta i;
      ) m;
      Printf.printf "\n"
    in
    if false then
    for i = 0 to maxdeg - 1 do
      Printf.printf "\nDegree %d:\n" i;
      List.iteri (fun i m ->
        Printf.printf "%04d    " i;
        p m
      ) memo.(i);
    done;
    (* END DEBUG *)
    fun (d,c) i ->
      let bi = Dst (d,c) in
      let k = I.k bi i in
      assert (k <= maxdeg);
      List.map (fun l ->
        DMap.fold (fun {deltas; base} ->
          let n = I.k dummy base in
          DMap.add {deltas; base = I.add bi n i}
        ) l DMap.empty
      ) memo.(k)

  (* DEBUG expand *) (* let _ = expand 2 *)

  let rec binom k n =
    if k = 0 then 1 else
    n * binom (k-1) (n-1) / k

  let shift vars x =
    assert (not (VSet.mem x vars));
    let (vnum, nvars) =
      let h = Hashtbl.create 101 in
      let n = ref 0 in
      VSet.iter
        (fun v -> Hashtbl.add h v !n; incr n) vars;
      (Hashtbl.find h, !n) in
    fun szch idx ->
    let elim d szch delta {deltas; base} factor dm =
      let p = I.k d base in
      let rec f i dm =
        if i = p+1 then dm else
        let d' = Array.copy deltas in
        let (a,b) = d'.(delta) in
        d'.(delta) <- if szch<0 then (a+i,b) else (a,b+i);
        let idx = {deltas = d'; base = I.add d (p-i) base} in
        let b = factor * pow szch i * binom i p in
        f (i+1) (DMap.add idx b dm) in
      f 0 dm in
    DMap.singleton
      { deltas = Array.make nvars (0,0)
      ; base = idx
      } 1 |>
    I.fold (fun (Dst (a, b) as d) _ dm ->
      let szch, c =
        if a = x then (- szch, b) else
        if b = x then (+ szch, a) else
        (0, a) in
      if szch = 0 then dm else
      DMap.fold (fun di k dm ->
        elim d szch (vnum c) di k dm
      ) dm dm
    ) idx
    (* DEBUG shift *)
    |> (fun di ->
      let p m =
        Printf.printf "0";
        DMap.iter (fun i n ->
          if n <> 0 then
          Printf.printf " + %d" n; print_delta i;
        ) m;
        Printf.printf "\n" in
      if false then p di;
      di
    )

  let _ =
    let _vars = VSet.of_list
      [ VId "c"; VId "b"; VNum 0 ] in
    let _idx =
      one
      |> I.add (Dst (VNum 0, VId "a")) 2
      |> I.add (Dst (VId "a", VId "c")) 2
    in
    (* shift _vars (VId "a") (+1) _idx *) ()
  (* END DEBUG *)

end

(* quantitative contexts and their operations *)
module Q: sig
  type ctx
  val vars: ctx -> VSet.t
  val empty: ctx
  val addv: ?sign: int -> ctx -> VSet.t -> ctx
  val delv: ?zero: bool -> ctx -> VSet.t -> ctx
  val incr: ctx -> var -> int -> (var * var) -> ctx
  val inc: ctx -> (Idx.t * (Idx.t * Idx.t) list * int) list -> ctx
  val eqc: ctx -> ctx -> unit
  val relax: pstate -> ctx -> ctx
  val merge: ?sign: int -> ctx list -> ctx
  val free: ctx -> Idx.t -> ctx
  val lift: ?sign: int -> ctx -> ctx -> ctx
  val subst: ctx -> id list -> var list -> ctx
  val frame: ctx -> ctx -> ctx * ctx
  val restore: ctx -> ctx -> VSet.t -> ctx
  val solve: ?dumps:(string * ctx) list -> ctx * ctx -> unit
end = struct
  module M = Map.Make(Idx)
  type ctx = { cvars: VSet.t; cmap: int M.t }

  let newv ?(sign=0) () =
    Clp.add_column
      { Clp.column_obj = 0.
      ; Clp.column_lower = if sign <= 0 then -. max_float else 0.
      ; Clp.column_upper = if sign >= 0 then max_float else 0.
      ; Clp.column_elements = [| |]
      };
    if debug > 3 && sign <> 0 then
      Printf.printf "sign of %d is %d\n" (Clp.number_columns () - 1) sign;
    Clp.number_columns () - 1

  let row_ ?(lo=0.) ?(up=0.) l k =
    let row_elements = Array.of_list
      (List.map (fun (i, w) -> (i, float_of_int w)) l) in
    Clp.add_row
      { Clp.row_lower = float_of_int k +. lo
      ; Clp.row_upper = float_of_int k +. up
      ; row_elements
      }

  let row ?(lo=0.) ?(up=0.) v' l k =
    if debug > 1 then begin
      if lo <> 0. || up <> 0. then () else
      let open Printf in
      let c = function
        | (v, w) when w = 1 -> sprintf "v%d" v
        | (v, w) -> sprintf "%d * v%d" w v in
      printf "v%d = %d" v' k;
      List.iter (fun x -> printf " + %s" (c x)) l;
      print_newline ()
    end;
    let l = List.map (fun (v, k) -> (v, -k)) l in
    row_ ~lo ~up ((v', 1) :: l) k

  let gerow v1 v2 c =
    row ~lo:0. ~up:max_float v1 [(v2, c)] 0

  let vars c = c.cvars

  let empty = {cvars = VSet.empty; cmap = M.empty}

  let addv ?(sign=0) c vs =
    assert (VSet.is_empty (VSet.inter (vars c) vs));
    let cvars = VSet.union [vars c; vs] in
    let cmap = Idx.fold
      (fun m i ->
        let v =
          try M.find i c.cmap with
          | Not_found -> newv ~sign () in
        M.add i v m)
      M.empty cvars in
    {cvars; cmap}

(*
  val expand: int -> var * var -> t -> int DMap.t list
  val shift: VSet.t -> var -> int -> t -> int DMap.t
*)
  let incr {cmap=m;cvars=v} a szch (cl,cu) =
    let module DM = Idx.DMap in
    let vma = VSet.remove a v in
    let shift = Idx.shift vma a in
    let expand = Idx.expand (VSet.cardinal vma) (cl,cu) in
    let m', cm =
      M.fold (fun i v (m', cm) ->
        let v' = newv () in
        let m' = M.add i v' m' in
        let l = List.map
          (fun di -> (newv (), di))
          (expand i) in
        row ~lo:0. ~up:max_float v'
          (List.map (fun (v,_) -> (v,1)) l) 0;
        let cm =
          List.fold_left (fun cm (v', dev) ->
            DM.fold (fun di k cm ->
              let ro =
                ((v', k), `D (dev, i)) ::
                try DM.find di cm
                with Not_found -> [] in
              DM.add di ro cm
            ) dev cm
          ) cm l in
        let cm =
          DM.fold (fun di k cm ->
            let ro =
              ((v, -k), `I (i)) ::
              try DM.find di cm
              with Not_found -> [] in
            DM.add di ro cm
          ) (shift szch i) cm in
        (m', cm)
      ) m (M.empty, DM.empty) in
    (*
    print_newline();
    *)
    DM.fold (fun _ ro () ->
      let p m =
        Printf.printf "0";
        Idx.DMap.iter (fun i n ->
          if n <> 0 then
          Printf.printf " + %d" n; Idx.print_delta i;
        ) m
      in
      let _f1 = function
        | ((_,k), `D (dev,_)) ->
          Printf.printf " %d {{" k; p dev; print_string "}}"
        | _ -> () in
      let _f2 = function
        | ((_,k), `I (i)) ->
          Printf.printf " %d {{" (-k); Idx.print i; print_string "}}"
        | _ -> () in
      (*
      List.iter _f1 ro; print_string " >= "; List.iter _f2 ro;
      print_newline ();
      *)
      row_ ~lo:0. ~up:0. (List.map fst ro) 0
    ) cm ();
    {cmap = m'; cvars = v}

  let inc ({cmap=m;_} as c) eqs =
    let bdgs = List.map
      begin fun (id, l, k) ->
        let mkmax (i1, i2) =
          let v = newv () in
          if debug > 1 then
            Printf.printf "v%d >= max(v%d, -v%d)\n" v
              (M.find i1 m) (M.find i2 m);
          gerow v (M.find i1 m) (+1);
          gerow v (M.find i2 m) (-1);
          (v, 1) in
        let v = newv () in
        row v ((M.find id m, 1) :: List.map mkmax l) k;
        (id, v)
      end eqs in
    { c with cmap =
      List.fold_left (fun m (i, v) -> M.add i v m) m bdgs }

  let delv ?(zero=true) c vs =
    assert (VSet.subset vs (vars c));
    let cvars = VSet.diff (vars c) vs in
    let m _ vo vo' =
      match vo, vo' with
      | Some _, Some _ -> vo
      | Some v, None -> if zero then row v [] 0; None
      | _, _ -> assert false in
    let c' = Idx.fold (fun m i -> M.add i 0 m) M.empty cvars in
    {cvars; cmap = M.merge m c.cmap c'}

  let eqc c1 c2 =
    assert (VSet.equal c1.cvars c2.cvars);
    let eqv i = row (M.find i c1.cmap) [(M.find i c2.cmap, 1)] 0 in
    Idx.fold (fun () -> eqv) () c1.cvars

  let relax ps c =
    let cm =
      Idx.fold (fun cm i ->
        let f sign (k, i') cm =
          (*
          if sign > 0 then
            print_string "relaxu"
          else if sign < 0 then
            print_string "relaxl"
          else
            print_string "relaxq";
          Idx.print i; print_newline ();
          print_string "  with"; Idx.print i'; print_newline ();
          *)
          let add i p cm =
            let l = try M.find i cm with Not_found -> [] in
            M.add i (p::l) cm in
          let xfer = newv ~sign () in
          cm |> add i (xfer, -1) |> add i' (xfer, k) in
        let blo, bup = Idx.range ps i in
        match Idx.eq (snd blo) i, Idx.eq (snd bup) i with
        | true, true -> cm
        | false, true -> f (-1) blo cm
        | true, false -> f (+1) bup cm
        | false, false ->
          if fst blo >= fst bup && Idx.eq (snd blo) (snd bup)
          then f 0 blo cm
          else (cm |> f (+1) bup |> f (-1) blo)
      ) M.empty c.cvars in
    let cmap =
      M.fold (fun i cl cmap ->
        let v = newv () in
        row v ((M.find i c.cmap, 1) :: cl) 0;
        M.add i v cmap
      ) cm c.cmap in
    {c with cmap }

  let merge ?(sign=0) cl =
    assert (List.for_all
      (fun {cvars;_} -> VSet.equal cvars (List.hd cl).cvars) cl
    );
    let m cmap' i =
      let v' = newv ~sign () in
      if debug > 1 then begin
        Printf.printf "v%d >= max(" v';
        ignore (List.fold_left (fun c {cmap=m;_} ->
            Printf.printf "%sv%d" (if c then ", " else "") (M.find i m);
            true
          ) false cl);
        Printf.printf ")\n";
      end;
      List.iter (fun {cmap;_} -> gerow v' (M.find i cmap) 1) cl;
      M.add i v' cmap' in
    let cvars = (List.hd cl).cvars in
    {cvars; cmap = Idx.fold m M.empty cvars}

  let free c idx =
    if debug > 1 then Printf.printf "v%d <= 0\n" (M.find idx c.cmap);
    row ~lo:(-. max_float) ~up:0. (M.find idx c.cmap) [] 0;
    { c with cmap = M.add idx (newv ~sign:(+1) ()) c.cmap }

  let lift ?(sign=(+1)) q q' =
    (* assert (VSet.subset (vars q) (vars q')); *)
    addv ~sign q (VSet.diff (vars q') (vars q))

  let subst {cvars; cmap} xl vl =
    let rename =
      let h = Hashtbl.create 11 in
      List.iter2 (Hashtbl.add h) xl vl;
      function
      | VId id as v ->
        (try Hashtbl.find h id with Not_found -> v)
      | VNum _ as v -> v in
    let module H = Hashtbl.Make(
        struct
          type t = Idx.t
          let equal = Idx.eq
          let hash _ = 42                                 (* OMG, fix me *)
        end
      ) in
    let h = H.create 257 in
    Idx.fold (fun () i ->
      match Idx.map rename i with
      | Some i' -> H.add h i' i
      | None -> ()
    ) () cvars;
    let cmap = Idx.fold (fun m i ->
        (*
        print_string "Index"; Idx.print i; print_newline ();
        List.iter (fun i' ->
          print_string "     "; Idx.print i'; print_newline ();
        ) (H.find_all h i);
        *)
        match H.find_all h i with
        | [] -> M.add i (newv ~sign:(+1) ()) m
        | [i'] -> M.add i (M.find i' cmap) m
        | payfor ->
          let v = newv () in
          row v (List.map (fun i -> (M.find i cmap,1)) payfor) 0;
          M.add i v m
      ) M.empty cvars in
    {cvars; cmap}

  let frame c1 c2 =
    let vx = newv ~sign:(+1) () and v1 = newv () and v2 = newv () in
    row v1 [(M.find Idx.one c1.cmap, 1); (vx, 1)] 0;
    row v2 [(M.find Idx.one c2.cmap, 1); (vx, 1)] 0;
    ( {c1 with cmap = M.add Idx.one v1 c1.cmap}
    , {c2 with cmap = M.add Idx.one v2 c2.cmap }
    )

  let restore c c' locals =
    assert (VSet.subset locals (vars c'));
    assert (VSet.subset locals (vars c));
    Idx.fold (fun c i ->
        if not (Idx.local locals i) then c else
        {c with cmap = M.add i (M.find i c'.cmap) c.cmap}
      ) c (vars c)

  let solve ?(dumps=[]) (cini, cfin) =
    let absl =
      Idx.fold begin fun l i ->
        let v = M.find i cini.cmap in
        let v' = newv () in
        gerow v' v 1; gerow v' v (-1);
        v' :: l
      end [] cini.cvars in
    let obj = Clp.objective_coefficients () in
    List.iter (fun v -> obj.(v) <- 1.) absl;
    let large = -200. in
    Idx.fold begin fun () i ->
      let o = float_of_int (Idx.obj i) in
      let v = M.find i cini.cmap in
      row ~lo:large ~up:max_float v [] 0;
      obj.(v) <- o;
    end () cini.cvars;
    flush stdout;
    Clp.set_log_level (if debug > 1 then 2 else 0);
    Clp.change_objective_coefficients obj;
    Clp.initial_solve ();
    while
      Clp.status () = 0 &&
      let sol = Clp.primal_column_solution () in
      Idx.fold begin fun again i ->
        if sol.(M.find i cini.cmap) <= large +. 1. then
          let v = M.find i cini.cmap in
          row ~lo:0. ~up:max_float v [] 0;
          true
        else again
      end false cini.cvars
    do
      Clp.primal ()
    done;
    match Clp.status () with
    | 0 ->
      let sol = Clp.primal_column_solution () in
      if debug > 1 then begin
        print_string "\nCoefficients:\n";
        for i = 0 to Array.length sol - 1 do
           if abs_float sol.(i) > 1e-6 then
           Printf.printf "v%d = %.2f\n" i sol.(i)
        done;
        print_newline ()
      end;
      let p c = Idx.fold
        (fun () i -> Idx.printk sol.(M.find i c.cmap) i)
        () (vars c) in
      List.iteri (fun n (info, c) ->
        Printf.printf "-- Dumpling %d: %s\n" n info;
        p c;
        print_newline ()
      ) dumps;
      p cini;
      if debug > 0 then (print_string "Final annotation:\n"; p cfin)
    | _ -> print_string "Sorry, I could not find a bound.\n"

end

(* let dumplings = ref [] *)

(* bye bye, we need to work on the cfg now

let analyze (fdefs, p) =
  (* generate and resolve constraints *)
  let open Idx in

  let glos = VSet.add (VNum 0) (file_globals (fdefs, p)) in
  let tmpret = "%ret" and vret = VId "%ret" in
  let rec gen_ qfuncs qret qbrk qseq =
    let gen = gen_ qfuncs qret qbrk in function

    | PTick (n, _) ->
      if n = 0 then qseq else
      let q = Q.inc qseq [one, [], n] in
      if n < 0 then Q.merge ~sign:(+1) [q] else q
    | PAssert _ -> qseq
    | PBreak {lpre; _} -> (* Q.relax lpre qbrk *) qbrk
    | PReturn (v, _) ->
      let q = Q.lift qret qseq in
      Q.delv (Q.subst q [tmpret] [v]) ~zero:false (VSet.of_list [vret])

    | PCall (ret, fname, args, _) ->
      let varl = List.map (fun x -> VId x) in
      let f = List.find (fun x -> x.fname = fname) fdefs in

      let tmps = List.map ((^) "%") f.fargs in
      let tmpset = VSet.of_list (varl tmps) in
      let argset = VSet.of_list (varl f.fargs) in
      let locset = VSet.of_list (varl f.flocs) in

      let qret = Q.addv ~sign:(+1) qseq (VSet.of_list [vret]) in
      let qret =
        match ret with
        | Some x -> Q.subst qret [x] [vret] (* XXX move *)
        | None -> qret in

      begin match
        try Some (List.assoc fname qfuncs)
        with Not_found -> None
      with

      | None -> (* unfold case *)
        let qcall = Q.addv ~sign:(+1) Q.empty (VSet.union [tmpset; Q.vars qseq]) in
        let qfun = Q.delv qret ~zero:false (VSet.of_list [vret]) in
        let qfun = Q.addv ~sign:(+1) qfun (VSet.union [argset; locset]) in
        let qbdy = gen_
          ((fname, (qcall, qret)) :: qfuncs)
          qret Q.empty qfun f.fbody in
        let qcall' = Q.addv ~sign:(+1) qbdy tmpset in
        let qcall' = Q.subst qcall' f.fargs (varl tmps) in (* XXX move *)
        let qcall' = Q.delv qcall' (VSet.union [argset; locset]) in
        Q.eqc qcall qcall';
        let q = Q.subst qcall tmps args in
        Q.delv q ~zero:false tmpset

      | Some (qcallf, qretf) -> (* recursive case *)
        let qcallf, qretf = Q.frame qcallf qretf in
        let qcallf = Q.lift qcallf qseq in
        let qcall = Q.subst qcallf tmps args in
        let qcall = Q.delv ~zero:false qcall tmpset in
        let qretf = Q.lift ~sign:(-1) qretf qseq in
        let locs = VSet.diff (Q.vars qseq) glos in
        let qretf = Q.restore qretf qcallf locs in
        Q.eqc qret qretf; qcall

      end

    | PInc (x, op, y, {lpre; lpost}) ->
      let opy, iopyz, izopy =
        let iyz = (y, VNum 0) and izy = (VNum 0, y) in
        match op with
        | OPlus -> LVar y, iyz, izy
        | OMinus -> LMult (-1, LVar y), izy, iyz in
      let q = Q.relax lpost qseq in

      if x = "x" then dumplings := ("after x+=N", q) :: !dumplings;

      let q' =
      begin match
        Logic.entails lpre opy CLe (LVar (VNum 0)),
        Logic.entails lpre opy CGe (LVar (VNum 0))
      with
      | true, true -> q
      | false, false -> assert false
      | true, false -> (* op y < 0 *) Q.incr q (VId x) (-1) iopyz
      | false, true -> (* op y > 0 *) Q.incr q (VId x) (+1) izopy
      end in

      if x = "x" then dumplings := ("before x+=N", q') :: !dumplings;
      Q.relax lpre q'


    | PSet (x, Some v, {lpre; _}) ->
      let q = Q.subst qseq [x] [v] in
      (* relax constant differences *)
      (* Q.relax lpre q *) q

    | PSet (x, None, _) ->
      let vars = VSet.remove (VId x) (Q.vars qseq) in
      VSet.fold begin fun u q ->
        Q.free (Q.free q (dst (u, VId x))) (dst (VId x, u))
      end vars qseq

    | PSeq (p1, p2, _) ->
      let qpre2 = gen qseq p2 in
      begin match p1 with
      | PLoop _ -> dumplings := ("after a loop", qpre2) :: !dumplings
      | PAssert _ -> dumplings := ("after an assert", qpre2) :: !dumplings
      | _ -> ()
      end;
      let qpre1 = gen (Q.merge [qpre2]) p1 in
      qpre1

    | PLoop (p, {lpre; _}) ->
      let qinv = Q.merge [qseq] in
      let qinv' = gen_ qfuncs qret qseq qinv p in
      Q.eqc qinv qinv';
      qinv'

    | PIf (_, p1, p2, _) ->
      let qpre1 = gen qseq p1 in
      let qpre2 = gen qseq p2 in
      Q.merge [qpre1; qpre2]

    in

  let q = Q.addv ~sign:(+1) Q.empty glos in
  let qret = Q.addv ~sign:(+1) q (VSet.singleton (VId "%ret")) in
  let qpre = gen_ [] qret Q.empty q p in
  Q.solve ~dumps:(!dumplings) (qpre, q)
*)

type ('b, 'a) ba = { bef: 'b; aft: 'a }

let analyze glos {fbody=bs; _} =
  let dumplings = ref [] in

  (* 1. logical analysis (per-block) *)

  let log blk =
    let ni = List.length blk.binsts in
    let log = Array.make ni {bef=[]; aft=[]} in
    List.fold_left (fun (bef, n) i ->
      let aft = match i with
        | ITick _ -> bef
        | IAssert c -> Logic.of_cond c @ bef
        | IInc (id, op, v) -> Logic.incr id op v bef
        | ISet (id, vo) -> Logic.set id vo bef
        | ICall _ -> [] (* reset all knowledge *)
      in
      log.(n) <- {bef; aft};
      (aft, n+1)
    ) ([], 0) blk.binsts |> ignore;
    log in

  (* 2. quantitative analysis *)

  let qret = ref Q.empty in
  let cs =
    (* this is the quantitative contexts
     * at block borders *)
    Array.init (Array.length bs)
      (fun i ->
        let ret, sign =
          match bs.(i).bjump with
          | JJmp bl -> false, if List.exists ((>=) i) bl then +1 else 0
          | JRet _  -> true,  +1 in
        let bef = Q.addv Q.empty glos in
        let aft = Q.addv ~sign Q.empty glos in
        if ret then qret := aft;
        {bef; aft}
      ) in

  Array.iteri (fun i blk ->
    let {bef; aft} = cs.(i) in
    let log = log blk in
    let inum = ref (List.length blk.binsts) in

    (* 2.1. merge after contexts *)
    let () =
      let befs =
        match blk.bjump with
        | JJmp bl -> List.map (fun b -> cs.(b).bef) bl
        | JRet _ -> [] in
      if befs <> [] then
        Q.eqc (Q.merge befs) aft
    in

    (* 2.2 process block instructions *)
    List.fold_right (fun i q ->

      let {bef=lbef; aft=laft} = log.(decr inum; !inum) in

      match i with
      | ITick n ->
        if n = 0 then q else
        let q = Q.inc q [Idx.one, [], n] in
        if n < 0 then Q.merge ~sign:(+1) [q] else q
      | IAssert _ -> q
      | IInc (x, op, y) ->
        let opy, iopyz, izopy =
          let iyz = (y, VNum 0) and izy = (VNum 0, y) in
          match op with
          | OPlus -> LVar y, iyz, izy
          | OMinus -> LMult (-1, LVar y), izy, iyz in
        let q = Q.relax laft q in
        if x = "x" then dumplings := ("after x+=N", q) :: !dumplings;
        let q' =
        begin match
          Logic.entails lbef opy CLe (LVar (VNum 0)),
          Logic.entails lbef opy CGe (LVar (VNum 0))
        with
        | true, true -> q
        | false, false -> assert false
        | true, false -> (* op y < 0 *) Q.incr q (VId x) (-1) iopyz
        | false, true -> (* op y > 0 *) Q.incr q (VId x) (+1) izopy
        end in
        if x = "x" then dumplings := ("before x+=N", q') :: !dumplings;
        Q.relax lbef q'
      | ISet (_x, _) ->
        failwith "ISet is not implemented yet"
      | ICall _ ->
        failwith "ICall is not implemented yet"

    ) blk.binsts aft |> Q.eqc bef;

  ) bs;

  let {bef=qini; _} = cs.(0) in
  Q.solve ~dumps:(!dumplings) (qini, !qret)

let _ =
  let f tick =
    let (_, pmain) =
      stdin
      |> Parse.pa_file
      |> Tools.clean_file in
    let (_, pmain) =
      if tick then Tools.auto_tick ([], pmain)
              else ([], pmain) in
    let glos = file_globals ([], pmain) in
    let glos = VSet.add (VNum 0) glos in
    let fmain =
      Cfg.of_func
        { fname="main"; fargs=[]
        ; flocs=[]; fbody=pmain} in
    Cfg.pp_func fmain;
    analyze glos fmain
  in
  if Array.length Sys.argv > 1 then
  match Sys.argv.(1) with
  | "-tc"     -> f true
  | "-tctick" -> f false
  | _ -> ()
