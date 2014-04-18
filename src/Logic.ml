(* simple abstract program state and logical entailment *)

open Parse

module Id = struct type t = id  let compare = compare end
module S = Set.Make(Id)
module M = struct
  include Map.Make(Id)
  let coeff id m =
    try find id m with Not_found -> 0
  let set = add
  let add id n m =
    let c = coeff id m in
    set id (c+n) m
  let vars vs m =
    fold (fun k c vs -> S.add k vs) m vs
end

type assn = A of int M.t * int
type aps = assn list

let add c v (A (m, k) as assn) =
  if c = 0 then assn else
  match v with
  | VNum n -> A (m, k - c * n)
  | VId x -> A (M.add x c m, k)

let assn_of_cond (Cond (v1, v2, k) (* v2 - v1 <= - k - 1 *)) =
  add 1 v2 (add (-1) v1(A (M.empty, -k - 1)))

let assn_negate (A (m, k)) =
  A (M.map (fun n -> -n) m, -k - 1)

let assn_incr id op delta (A (m, _) as assn) =
  let s = match op with OPlus -> -1 | OMinus -> +1 in
  add (s * M.coeff id m) delta assn

let aps_incr id op delta = List.map (assn_incr id op delta)

let aps_set id v ps =
  (* forget everything concerning the assigned variable *)
  add 1 v (add (-1) (VId id) (A (M.empty, 0))) ::
  add (-1) v (add 1 (VId id) (A (M.empty, 0))) ::
  List.filter (fun (A (m, _)) -> M.coeff id m = 0) ps


(* poor man's decision procedure *)

let rec vars = function
  | A (m, _) :: assns -> M.vars (vars assns) m
  | [] -> S.empty

let rec gcd a b =
  if a = 0 || b = 0 then a + b else
  if a < b
    then gcd a (b mod a)
    else gcd (a mod b) b

let assn_combine (c1, A (m1, k1)) (c2, A (m2, k2)) =
  let c1, c2 = let g = gcd c1 c2 in (c1/g, c2/g) in
  let h = function Some n -> n | None -> 0 in
  let f _ a b =
    let o = c2 * h a + c1 * h b in
    if o = 0 then None else Some o in
  A (M.merge f m1 m2, c2 * k1 + c1 * k2)

let elim id ps =
  let rec part3 p n rest  = function
    | [] -> (p, n, rest)
    | A (m, _) as assn :: ps' ->
      let c = M.coeff id m in
      if c > 0 then part3 ((c, assn) :: p) n rest ps'
      else if c < 0 then part3 p ((-c, assn) :: n) rest ps'
      else part3 p n (assn :: rest) ps' in
  let p, n, rest = part3 [] [] [] ps in
  let prod f l1 l2 =
    List.fold_left (* product function on lists *)
      (fun x a -> List.fold_left (fun y b -> f a b :: y) x l2)
      [] l1 in
  let comb = prod assn_combine p n in
  assert (List.for_all (fun (A (m, _)) -> M.coeff id m = 0) comb); (* XXX *)
  comb @ rest

let aps_is_valid ps =
  let simpl = S.fold elim (vars ps) ps in
  let dec_simple (A (m, k)) =
    assert (M.for_all (fun _ c -> c = 0) m); (* XXX *)
    0 <= k in
  List.fold_left (fun b assn -> dec_simple assn && b) true simpl


(* applications *)

let aps_add a ps =
  (* do not add consequences *)
  if not (aps_is_valid (assn_negate a :: ps)) then ps else a :: ps

let rec aps_fix ps f =
  let x, ps' = f ps in
  let rec residue trimmed r = function
    | assn :: assns ->
      if not (aps_is_valid (assn_negate assn :: ps'))
        then residue trimmed (assn :: r) assns
        else residue true r assns
    | [] -> (trimmed, r) in
  let trimmed, ps'' = residue false [] ps in
  if trimmed then aps_fix ps'' f else (x, ps)

let aps_entails ps x op delta u =
  (* check if ps entails x `op` delta \in [x, u] U [u, x] *)
  let s = match op with OPlus -> +1 | OMinus -> -1 in
  (* x `op` delta <= x - 1  /\  x `op` delta <= u - 1 *)
  let disj1 =
    [ add s delta (A (M.empty, -1))
    ; add s delta (add (-1) u (add 1 (VId x) (A (M.empty, -1)))) ] in
  (* u <= x `op` delta - 1  /\  x <= x `op` delta - 1 *)
  let disj2 =
    [ add (-s) delta (add 1 u (add (-1) (VId x) (A (M.empty, -1))))
    ; add (-s) delta (A (M.empty, -1)) ] in
  (* check entailment by refutation *)
  not (aps_is_valid (disj1 @ ps)) && not (aps_is_valid (disj2 @ ps))


(* pretty printing *)
let pp_aps ps =
  let rec ppl z sep pp = function
    | [] -> print_string z
    | [x] -> pp x
    | x :: ((y :: _) as xs) ->
      pp x; print_string (sep y);
      ppl z sep pp xs in
  let ppa (A (m, k)) =
    let sep (_, c) =
      if c < 0 then " - "
      else if c > 0 then " + "
      else "" in
    let p (k, c) =
      let c = abs c in
      if c <> 1 then (print_int c; print_string " ");
      print_string k in
    let bdgs = M.bindings m in
    (try if snd (List.hd bdgs) < 0 then print_string "-"
    with Failure _ -> ());
    ppl "0" sep p bdgs;
    print_string " <= ";
    print_int k in
  print_string "{ ";
  ppl "True" (fun _ -> " /\\ ") ppa ps;
  print_string " }"


(* unit tests *)
let _ =
  if Array.length Sys.argv < 2 || Sys.argv.(1) <> "-tlogic" then () else

  (* semantics of assertions *)
  let get h v = List.assoc v h in
  let rec sum h = function
    | (id, c) :: ids -> c * get h id + sum h ids
    | [] -> 0 in
  let assn_sem h (A (m, k)) =
    sum h (M.bindings m) <= k in
  let rec sem h = function
    | a :: al -> assn_sem h a && sem h al
    | [] -> true in

  (* tests *)
  let c1 = Cond (VNum 0, VNum 1, 0)
  and c2 = Cond (VNum 1, VNum 0, 1)
  and c3 = Cond (VId "x", VNum 0, 1)
  and c4 = Cond (VId "x", VNum 0, 2)
  and c5 = Cond (VNum 1, VId "y", 2)
  and c6 = Cond (VNum 1, VId "x", 0)
  and c7 = Cond (VId "y", VId "x", 0)
  and h1 = [("x", 1); ("y", 0)]
  in

  assert (sem [] [] = true);
  assert (sem [] [assn_of_cond c1] = false);
  assert (sem [] [assn_negate (assn_of_cond c1)] = true);
  assert (sem [] [assn_of_cond c2] = false);
  assert (sem [] [assn_negate (assn_of_cond c2)] = true);
  assert (sem h1 [assn_of_cond c3] = false);
  assert (sem h1 [assn_negate (assn_of_cond c3)] = true);
  assert (sem h1 [assn_of_cond c4] = false);
  assert (sem h1 [assn_negate (assn_of_cond c4)] = true);
  assert (sem h1 [assn_of_cond c5] = false);
  assert (sem h1 [assn_negate (assn_of_cond c5)] = true);
  assert (sem h1 [assn_of_cond c6] = false);
  assert (sem h1 [assn_of_cond c7] = false);
  assert (sem h1 [assn_negate (assn_of_cond c7)] = true);

  prerr_endline "Logic tests passed.";
  ()
