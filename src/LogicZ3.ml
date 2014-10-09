(* simple abstract program state and logical entailment *)

open Parse

let ctx = Z3.mk_context []
let isort = Z3.Arithmetic.Integer.mk_sort ctx

type pstate = Z3.Expr.expr

let convvar =
  let open Z3.Arithmetic.Integer in
  let module V = struct type t = var let compare = compare end in
  let module M = Map.Make(V) in
  let m = ref M.empty in
  fun v ->
    try M.find v !m with Not_found ->
    let e =
      match v with
      | VId id -> mk_const_s ctx id
      | VNum n -> mk_numeral_i ctx n
    in m := M.add v e !m; e

let of_cond = function
  | CTest (l1, cmp, l2) ->
    let open Z3.Arithmetic in
    let rec convl = function
      | LAdd (l1, l2) -> mk_add ctx [convl l1; convl l2]
      | LSub (l1, l2) -> mk_sub ctx [convl l1; convl l2]
      | LMult (k, l) -> mk_mul ctx [convvar (VNum k); convl l]
      | LVar v -> convvar v
    in begin match cmp with
    | CLe -> mk_le ctx (convl l1) (convl l2)
    | CGe -> mk_ge ctx (convl l1) (convl l2)
    | CLt -> mk_lt ctx (convl l1) (convl l2)
    | CGt -> mk_gt ctx (convl l1) (convl l2)
    end
  | CNonDet -> Z3.Boolean.mk_true ctx

let top = Z3.Boolean.mk_true ctx
let bottom = Z3.Boolean.mk_false ctx

let forget id ps =
  let open Z3.Expr in
  let old = mk_const_s ctx id isort in
  let neo = mk_fresh_const ctx id isort in
  (substitute_one ps old neo, neo)

let set id vo ps =
  let ps', _ = forget id ps in
  match vo with
  | Some v -> Z3.Boolean.mk_and ctx
    [ Z3.Boolean.mk_eq ctx (convvar (VId id)) (convvar v)
    ; ps' ]
  | None -> ps'

let incr id op delta ps =
  let ps', neo = forget id ps in
  let e =
    match op with
    | OPlus -> Z3.Arithmetic.mk_add ctx [neo; convvar delta]
    | OMinus -> Z3.Arithmetic.mk_sub ctx [neo; convvar delta]
  in Z3.Boolean.mk_and ctx [Z3.Boolean.mk_eq ctx (convvar (VId id)) e; ps']

let unsat ps =
  let open Z3.Solver in
  let solver = mk_solver ctx None in
  (* set_parameters solver (Z3.Params.mk_params ctx); *)
  add solver [ps];
  check solver [] <> SATISFIABLE


(* applications *)

let imp ps a = unsat (Z3.Boolean.mk_and ctx [ps; Z3.Boolean.mk_not ctx a])
let entails ps l1 c l2 = imp ps (of_cond (CTest (l1, c, l2)))
let conj ps1 ps2 = Z3.Boolean.mk_and ctx [ps1; ps2]
let merge ps1 ps2 = Z3.Boolean.mk_or ctx [ps1; ps2]
let rec fix _ps _f = Z3.Boolean.mk_true ctx
(*
  let x, ps' = f ps in
  let rec residue trimmed r = function
    | assn :: assns ->
      if imp ps' assn
        then residue trimmed (assn :: r) assns
        else residue true r assns
    | [] -> (trimmed, r) in
  let trimmed, ps'' = residue false [] ps in
  if trimmed then fix ps'' f else (x, ps)
*)


let range ps = function
  | VNum n -> (Some n, Some n)
  | VId _ as v ->
    let bounds =
      [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9
      ; 10; 20; 30; 40; 50; 60; 70; 80; 90
      ; 100; 200; 300; 400; 500; 600; 700; 800; 900 ] in
    let lb = ref None and ub = ref None in
    List.iter (fun n ->
      let cmp c n = entails ps (LVar v) c (LVar (VNum n)) in
      if cmp CLe (-n) then ub := Some (-n);
      if !ub = None && cmp CLe n then ub := Some n;
      if cmp CGe n then lb := Some n;
      if !lb = None && cmp CGe (-n) then lb := Some (-n);
    ) bounds;
    (!lb, !ub)

(* pretty printing *)
let pp ps = print_string (Z3.Expr.to_string ps)
