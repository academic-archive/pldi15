(* simple abstract program state and logical entailment *)

open Parse

(*
  The meaning of the assertion ALt l1 l2 k
  is \sum l1 < \sum l2 + k.
  An abstract program state is simply a list
  of assertions.
*)
type assn = ALt of id list * id list * int
type aps = assn list

let rec drop elt = function
  | e :: es -> if e = elt then es else e :: drop elt es
  | [] -> raise Not_found

let add_l1 v (ALt (l1, l2, k)) =
  match v with
  | VNum n -> ALt (l1, l2, -n + k)
  | VId id ->
    try ALt (l1, drop id l2, k)
    with Not_found -> ALt (id :: l1, l2, k)

let add_l2 v (ALt (l1, l2, k)) =
  match v with
  | VNum n -> ALt (l1, l2, n + k)
  | VId id ->
    try ALt (drop id l1, l2, k)
    with Not_found -> ALt (l1, id :: l2, k)

let assn_of_cond (Cond (v1, v2, k) (* v2 < v1 - k *)) =
  add_l1 v2 (add_l2 v1 (ALt ([], [], -k)))

let assn_negate (ALt (l1, l2, k)) = ALt (l2, l1, 1 - k)

let assn_incr id op delta (ALt (l1, l2, _) as asn) =
  let add1, add2 =
    match op with
    | OPlus -> add_l1, add_l2
    | OMinus -> add_l2, add_l1 in
  let mem1 = List.mem id l1 in
  let mem2 = List.mem id l2 in
  if mem1 && mem2 then
    failwith "assertion invariant broken"
  else if mem1 then add2 delta asn
  else if mem2 then add1 delta asn
  else asn

let aps_incr id op delta = List.map (assn_incr id op delta)

let aps_set id v ps =
  (* forget everything concerning the assigned variable *)
  let rec purge = function
    | ALt (l1, l2, _) as assn :: assns ->
      if List.mem id l1 || List.mem id l2
        then purge assns
        else assn :: purge assns
    | [] -> [] in
  add_l1 v (ALt ([], [id], 1)) :: add_l2 v (ALt ([id], [], 1)) ::
    purge ps


(* poor man's decision procedure *)

module IdSet = Set.Make(struct type t = id  let compare = compare end)

let vars ps =
  let f = List.fold_left (fun a b -> IdSet.add b a) in
  let vs =
    List.fold_left
      (fun s (ALt (l1, l2, _)) -> (f (f s l2) l1))
      IdSet.empty
      ps in
  IdSet.elements vs

let assn_combine (ALt (l11, l21, k1)) (ALt (l12, l22, k2)) =
  List.fold_left (fun assn id1 -> add_l1 (VId id1) assn)
    (List.fold_left (fun assn id2 -> add_l2 (VId id2) assn)
      (ALt (l11, l21, k1 + k2 - 1)) l22)
    l12

let elim id ps =
  let rec part3 lo hi rest  = function
    | [] -> (lo, hi, rest)
    | ALt (l1, l2, _) as assn :: ps' ->
      if List.mem id l1 then part3 (assn :: lo) hi rest ps'
      else if List.mem id l2 then part3 lo (assn :: hi) rest ps'
      else part3 lo hi (assn :: rest) ps' in
  let lo, hi, rest = part3 [] [] [] ps in
  let prod f l1 l2 =
    List.fold_left (* product function on lists *)
      (fun x a -> List.fold_left (fun y b -> f a b :: y) x l2)
      [] l1 in
  prod assn_combine lo hi @ rest

let aps_is_valid ps =
  let simpl = List.fold_left (fun a b -> elim b a) ps (vars ps) in
  let dec_simple = function
    | ALt ([], [], k) -> 0 < k
    | _ -> failwith "Logic: bug in aps_is_valid" in
  List.fold_left (fun b assn -> dec_simple assn && b) true simpl


(* applications *)

let aps_add a ps =
  if not (aps_is_valid (assn_negate a :: ps))
    then ps (* do not add consequences *)
    else a :: ps

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
  let delta_l1, delta_l2 =
    match op with
    | OPlus -> add_l1 delta, add_l2 delta
    | OMinus -> add_l2 delta, add_l1 delta in
  (* x `op` delta < x  /\  x `op` delta < u *)
  let disj1 =
    [ delta_l1 (ALt ([], [], 0))
    ; delta_l1 (add_l2 u (ALt ([x], [], 0))) ] in
  (* u < x `op` delta  /\  x < x `op` delta *)
  let disj2 =
    [ delta_l2 (add_l1 u (ALt ([], [x], 0)))
    ; delta_l2 (ALt ([], [], 0)) ] in
  (* check entailment by refutation *)
  not (aps_is_valid (disj1 @ ps)) && not (aps_is_valid (disj2 @ ps))


(* pretty printing *)
let pp_aps ps =
  let rec ppl z sep pp = function
    | [] -> print_string z
    | [x] -> pp x
    | x :: xs -> pp x; print_string sep; ppl z sep pp xs in
  let ppa (ALt (l1, l2, k)) =
    ppl "0" " + " print_string l1;
    print_string " < ";
    if l2 = [] then print_int k else begin
      ppl "0" " + " print_string l2;
      if k < 0 then (print_string " - "; print_int (-k))
      else if k > 0 then (print_string " + "; print_int k)
    end in
  print_string "{ ";
  ppl "True" " /\\ " ppa ps;
  print_string " }"


(* unit tests *)
let _ =
  if Array.length Sys.argv < 2 || Sys.argv.(1) <> "-tlogic" then () else

  (* semantics of assertions *)
  let get h v = List.assoc v h in
  let rec sum h = function
    | id :: ids -> get h id + sum h ids
    | [] -> 0 in
  let assn_sem h (ALt (l1, l2, k)) =
    sum h l1 < sum h l2 + k in
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
