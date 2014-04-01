(* abstract program states *)

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

let negate (ALt (l1, l2, k)) = ALt (l2, l1, 1 - k)

let assn_incr id op delta (ALt (l1, l2, _) as asn) =
  let add1, add2 =
    match op with
    | OPlus -> add_l1, add_l2
    | OMinus -> add_l2, add_l1 in
  if List.mem id l1 && List.mem id l2 then
    failwith "assertion invariant broken"
  else if List.mem id l1 then add2 delta asn
  else if List.mem id l2 then add1 delta asn
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

let rec aps_loop ps1 ps2 =
  (* keep only the unchanged assertions *)
  match ps1 with
  | a :: ps1' ->
    if List.mem a ps2
      then a :: aps_loop ps1' ps2
      else aps_loop ps1' ps2
  | [] -> []


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
  assert (sem [] [negate (assn_of_cond c1)] = true);
  assert (sem [] [assn_of_cond c2] = false);
  assert (sem [] [negate (assn_of_cond c2)] = true);
  assert (sem h1 [assn_of_cond c3] = false);
  assert (sem h1 [negate (assn_of_cond c3)] = true);
  assert (sem h1 [assn_of_cond c4] = false);
  assert (sem h1 [negate (assn_of_cond c4)] = true);
  assert (sem h1 [assn_of_cond c5] = false);
  assert (sem h1 [negate (assn_of_cond c5)] = true);
  assert (sem h1 [assn_of_cond c6] = false);
  assert (sem h1 [assn_of_cond c7] = false);
  assert (sem h1 [negate (assn_of_cond c7)] = true);

  prerr_endline "Logic tests passed.";
  ()
