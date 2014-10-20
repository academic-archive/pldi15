(* simple abstract program state and logical entailment *)

open Parse

module Id = struct type t = id let compare = compare end
module S = Set.Make(Id)

module L = struct
  (* linear sums *)
  include Map.Make(Id)
  type sum = {m: int t; k: int}

  let const k = {m = empty; k}

  let coeff id {m;_} =
    try find id m with Not_found -> 0

  let set x c {m;k}= {m = add x c m; k}

  let addl id n m =
    let c = coeff id m in
    set id (c+n) m

  let addk k' {m; k} = {m; k = k + k'}

  let mult c {m; k} =
    {m = map (fun n -> c * n) m; k = c * k}

  let vars vs s =
    fold (fun k c vs -> S.add k vs) s.m vs

  let plus c {m = m1; k = k1} {m = m2; k = k2} =
    let h = function Some n -> n | None -> 0 in
    let f _ a b =
      let o = c * h a + h b in
      if o = 0 then None else Some o in
    {m = merge f m1 m2; k = c * k1 + k2}

  let pp {m; k} =
    let open Printf in
    let psign first c =
      if first then
        (if c < 0 then printf "-")
      else
        if c < 0 then printf " - "
        else printf " + " in
    let pterm x c =
      if abs c <> 1 then
        printf "%d " (abs c);
      printf "%s" x in
    let rec p first = function
      | (x, c) :: tl ->
        psign first c; pterm x c; p false tl
      | [] -> () in
    let bdgs =
      List.filter (fun (_, c) -> c <> 0)
        (bindings m) in
    p true bdgs;
    if k <> 0 then
      (psign (bdgs = []) k; printf "%d" (abs k))
end

type ineq = L.sum (* sum <= 0 *)
type pstate = ineq list

let plusv c v l =
  if c = 0 then l else
  match v with
  | VNum n -> L.addk (n * c) l
  | VId x -> L.addl x c l

let of_cond = function
  | CTest (l1, cmp, l2) ->
    let rec addl k s = function
      | LAdd (l1, l2) -> addl k (addl k s l1) l2
      | LSub (l1, l2) -> addl (-k) (addl k s l1) l2
      | LMult (k', l) -> addl (k * k') s l
      | LVar v -> plusv k v s in
    let a1, a2, b =
      match cmp with
      | CLe -> 1, -1, 0
      | CGe -> -1, 1, 0
      | CLt -> 1, -1, 1
      | CGt -> -1, 1, 1
    in [addl a1 (addl a2 (L.const b) l2) l1]
  | CNonDet -> []

let top = []
let bottom = [L.const 1]

let ineq_incr id op delta l =
  let s = match op with OPlus -> -1 | OMinus -> +1 in
  plusv (s * L.coeff id l) delta l

let set id vo ps =
  (* forget everything concerning the assigned variable *)
  let ps' = List.filter (fun i -> L.coeff id i = 0) ps in
  match vo with
  | None -> ps'
  | Some ((VId id') as v') ->
    plusv (-1) (VId id) (plusv (+1) v' (L.const 0)) ::
    plusv (+1) (VId id) (plusv (-1) v' (L.const 0)) ::
    List.fold_left (fun ps' i ->
        let c = L.coeff id' i in
        if c = 0 then ps' else
        L.addl id' (-c) (L.addl id (+c) i) :: ps'
      ) ps' ps
  | Some (VNum n) ->
    plusv (-1) (VId id) (L.const (+n)) ::
    plusv (+1) (VId id) (L.const (-n)) :: ps'

let incr id op delta =
  if delta = VId id
    then List.filter (fun i -> L.coeff id i = 0)
    else List.map (ineq_incr id op delta)

(* decision procedure (calling Z3) *)

let ctx = Z3.mk_context []
let solver = Z3.Solver.mk_solver ctx None
let isort = Z3.Arithmetic.Integer.mk_sort ctx

let unsat ps =
  let cnvsum {L.m; k} =
    let open Z3.Arithmetic in
    let cnvk = Integer.mk_numeral_i ctx in
    let cnvv = Integer.mk_const_s ctx in
    let sum =
      L.fold (fun v n s ->
          mk_add ctx [mk_mul ctx [cnvk n; cnvv v]; s]
        ) m (cnvk k) in
    mk_le ctx sum (cnvk 0) in
  let open Z3.Solver in
  push solver;
  add solver (List.map cnvsum ps);
  let c = check solver [] in
  pop solver 1;
  c <> SATISFIABLE

(* applications *)

let imp ps a =
  let nega = L.addk 1 (L.mult (-1) a) in
  unsat (nega :: ps)

let conj ps1 ps2 = List.fold_left
    (fun ps a -> if imp ps a then ps else a :: ps)
    ps2 ps1

let merge ps1 ps2 =
  let ps2' = List.filter (imp ps1)  ps2 in
  let ps1' = List.filter (imp ps2)  ps1 in
  conj ps2' ps1'

let rec fix ps f =
  let x, ps' = f ps in
  let rec residue trimmed r = function
    | assn :: assns ->
      if imp ps' assn
        then residue trimmed (assn :: r) assns
        else residue true r assns
    | [] -> (trimmed, r) in
  let trimmed, ps'' = residue false [] ps in
  if trimmed then fix ps'' f else (x, ps)

let entails ps l1 c l2 =
  match of_cond (CTest (l1, c, l2)) with
  | [a] -> imp ps a
  | _ -> failwith "Logic.ml: bug in entails"

let range ps = function
  | VNum n -> (Some n, Some n)
  | VId v ->
    let upd f a = function
      | Some x -> Some (f a x)
      | None -> Some a in
    List.fold_left
      begin fun (lb, ub) a ->
        let c = L.coeff v a in
        let pred v' n = v=v' || n=0 in
        if c = 0 || not (L.for_all pred a.L.m)
          then (lb, ub) else
          if c < 0
            then (upd max (a.L.k / -c) lb, ub)
            else (lb, upd min (-a.L.k / c) ub)
      end (None, None) ps

(* pretty printing *)
let pp ps =
  let rec p = function
    | [] -> print_string "T"
    | [a] -> L.pp a; print_string " ≤ 0"
    | a :: tl -> L.pp a; print_string " ≤ 0 /\\ "; p tl in
  print_string "{ "; p ps; print_string " }"
