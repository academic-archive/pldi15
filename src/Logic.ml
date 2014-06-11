(* simple abstract program state and logical entailment *)

let show_progress = false

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

let bottom = [L.const 1]

let ineq_incr id op delta l =
  let s = match op with OPlus -> -1 | OMinus -> +1 in
  plusv (s * L.coeff id l) delta l

let set id vo ps =
  (* forget everything concerning the assigned variable *)
  let ps' = List.filter (fun i -> L.coeff id i = 0) ps in
  match vo with
  | None -> ps'
  | Some (VId id') ->
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


(* poor man's decision procedure *)

type div = { k : int; s : L.sum } (* k | s *)

let lcm a b =
  let rec gcd a b =
    if a = 0 || b = 0 then a + b else
    if a < b
      then gcd a (b mod a)
      else gcd (a mod b) b in
  let a = abs a and b = abs b in
  assert (a * b <> 0); (a * b) / gcd a b

let normi id ps =
  (* make sure id has the same coefficient everywhere *)
  let l = List.fold_left (fun l i -> lcm l (L.coeff id i)) 1 ps in
  let f m = L.mult (l / abs (L.coeff id m)) m in
  (List.map f ps, l)

let dbg x =
  (if show_progress then Printf.fprintf else Printf.ifprintf) stdout x
let uid = ref 0

let rec elim x (ps, ds) vars =
  let c = L.coeff x in
  let ps, irest = List.partition (fun i -> c i <> 0) ps in
  let ps, l = normi x ps in
  let ubs, lbs = List.partition (fun i -> c i > 0) ps in
  let ds, drest = List.partition (fun d -> c d.s <> 0) ds in
  let w = List.fold_left (fun w d -> lcm w d.k) 1 ds in
  List.exists begin fun glb ->
    let lbs' =  List.map (L.plus (-1) glb) lbs in
    let rec loop i =
      if i < 0 then false else
      let xeq = L.addk i glb in
      let ubs' = List.map (L.plus 1 xeq) ubs in
      let ds' =
        let trd {k; s} =
          { k = k * l
          ; s = L.plus 1 (L.mult (c s) xeq) (L.mult l s)
          } in
        let s = L.set x 0 xeq in
        {k = l; s} :: List.map trd ds in
      assert (List.for_all (fun i -> L.coeff x i = 0) (lbs' @ ubs')); (* XXX *)
      assert (List.for_all (fun d -> L.coeff x d.s = 0) ds');
      let id = !uid in uid := !uid + 1;
      dbg ">> (%d) attempt with i=%d\n" id i;
      let sb = sat (lbs' @ ubs' @ irest, ds' @ drest) vars in
      dbg "<< (%d) end of attempt with i=%d\n" id i;
      sb || loop (i-1)
    in loop (l * w - 1)
  end (
    if lbs = []
        (* this is not complete, but sound *)
      then [L.set x (-l) (L.const (-10_000))]
      else lbs
  )

and sat (ps, divs) = function
  | id :: vars -> elim id (ps, divs) vars
  | [] ->
    let zero {L.m;_} = assert (L.for_all (fun _ c -> c = 0) m) in (* XXX *)
    let deci s = zero s; dbg "  %d <= 0\n" s.L.k; s.L.k <= 0 in
    let decd {k; s} = zero s; dbg "  %d | %d\n" k s.L.k; s.L.k mod k = 0 in
    List.for_all deci ps && List.for_all decd divs

let sat (ps, divs) vars =
  uid := 0; sat (ps, divs) vars

let sat ps =
  let vars = List.fold_left L.vars S.empty ps
  in sat (ps, []) (S.elements vars)


(* applications *)

let imp ps a =
  let nega = L.addk 1 (L.mult (-1) a) in
  not (sat (nega :: ps))

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

let value ps = function
  | VNum n -> Some n
  | VId v ->
    let ubs, lbs = List.fold_left
      begin fun (ubs, lbs) a ->
        let c = L.coeff v a in
        if c = 0 || not (L.for_all (fun v' n -> v = v' || n = 0) a.L.m)
          then (lbs, ubs) else
          if c < 0
            then (ubs, a.L.k / -c :: lbs)
            else (-a.L.k / c :: ubs, lbs)
      end ([], []) ps in
    let rec inter us = function
      | l :: ls -> if List.mem l us then Some l else inter us ls
      | [] -> None in
    inter ubs lbs


(* pretty printing *)
let pp ps =
  let rec p = function
    | [] -> print_string "T"
    | [a] -> L.pp a; print_string " ≤ 0"
    | a :: tl -> L.pp a; print_string " ≤ 0 /\\ "; p tl in
  print_string "{ "; p ps; print_string " }"
