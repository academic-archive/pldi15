(* Slicing and normalizing CIL programs *)
open Cil
open Parse
module E = Errormsg


(* test if [v] must be tracked in the analysis *)
let is_tracked v =
  v.vglob = false && isIntegralType v.vtype

exception Unsupported

let rec transl_sum = function
  | Const (CInt64 (i, _, _)) ->
    LVar (VNum (Int64.to_int i))
  | Const (CChr c) ->
    transl_sum (Const (charConstToInt c))
  | Lval (Var vi, NoOffset) when is_tracked vi ->
    LVar (VId (vi.vname))
  | UnOp (Neg, e, _) ->
    LMult (-1, transl_sum e)
  | BinOp (PlusA, e1, e2, _) ->
    LAdd (transl_sum e1, transl_sum e2)
  | BinOp (MinusA, e1, e2, _) ->
    LSub (transl_sum e1, transl_sum e2)
  | BinOp (Mult, e, Const (CInt64 (i, _, _)), _)
  | BinOp (Mult, Const (CInt64 (i, _, _)), e, _) ->
    LMult (Int64.to_int i, transl_sum e)
  | _ -> raise Unsupported

let linearize =
  let rec add (x,n) = function
    | [] -> [(x, n)]
    | (y, m) :: tl when y = x ->
      (x, m+n) :: tl
    | p :: tl -> p :: add (x,n) tl
  in
  let rec f (m,k) mult = function
    | LVar (VNum n) -> (m, k+n*mult)
    | LVar (VId x) -> (add (x,mult) m, k)
    | LMult (n, l) -> f (m,k) (mult*n) l
    | LAdd (l1, l2) ->
      let m1,k1 = f (m,k) mult l1 in
      let m2,k2 = f (m1,k1) mult l2 in
      m2,k2
    | LSub (l1, l2) ->
      let m1,k1 = f (m,k) mult l1 in
      let m2,k2 = f (m1,k1) (-mult) l2 in
      m2,k2
  in f ([], 0) 1

(* simplify assignments *)
let transl_set gid v exp =
  try
    let m,k = linearize (transl_sum exp) in
    let cv = if List.mem_assoc v m then List.assoc v m else 0 in

    let rec repeat x n k =
      if n = 0 then k else
      PSeq (x (gid ()), repeat x (n-1) k, gid ()) in

    let deltas = List.fold_left
      (fun ds (x,n) ->
        let n = if x = v && n > 0 then n-1 else n in
        let x = if x = v then "%tmp" else x in
        if n >= 0
          then repeat (fun i -> PInc (v, OPlus, VId x, i)) n ds
          else repeat (fun i -> PInc (v, OMinus, VId x, i)) (-n) ds
      )
      (if k <> 0
        then PInc (v, OPlus, VNum k, gid ())
        else PTick (0, gid ())
      ) m
    in
    let p =
      if cv = 0 then
        match deltas with
        | PSeq (PInc (_, OPlus, v', id1), p, id2) ->
          PSeq (PSet (v, Some v', id1), p, id2)
        | PInc (v, OPlus, VNum n, id) ->
          PSet (v, Some (VNum n), id)
        | _ ->
          PSeq (PSet (v, Some (VNum 0), gid ()), deltas, gid ())
      else if cv < 0 then
        PSeq (PSet (v, Some (VNum 0), gid ()), deltas, gid ())
      else
        deltas in
    if cv = 1 || cv = 0 then p else
    PSeq (PSet ("%tmp", Some (VId v), gid ()), p, gid ())

  with Unsupported -> PSet (v, None, gid ())

let transl_cond = function
  | BinOp ((Ge | Le | Gt | Lt) as bop, e1, e2, _) ->
    let cop =
      match bop with
      | Ge -> CGe | Le -> CLe
      | Gt -> CGt  | Lt -> CLt
      | _ -> assert false in
    (try CTest (transl_sum e1, cop, transl_sum e2)
    with Unsupported -> CNonDet)
  | _ -> CNonDet


(*
  the following program operations can be
  assigned a cost in the [slice] function
  below
*)
type prog_op =
  | OpExp of exp
  | OpSet | OpTest
  | OpBreak | OpLoop
  | OpReturn | OpSeq


(* compile a CIL program into a [Parse.prog] program *)
let slice cost {fileName; globals; _} =

  let gid =
    let i = ref (-1) in
    fun () -> incr i; !i in

  let check_lvalue loc = function
    | (Var v, NoOffset) when is_tracked v ->
      Some v.vname
    | (Var _, _) ->
      None
    | (_, _) -> E.s (
        E.error "%s:%d unsupported lvalue"
          loc.file loc.line
      )
  in

  let rec seq a b =
    match a with
    | PSeq (a1, a2, id) ->
      seq a1 (seq a2 b)
    | PTick (n1, _) ->
      begin match b with
      | PTick (n2, id) -> PTick (n1 + n2, id)
      | PSeq (PTick (n2, id), b', id') ->
        PSeq (PTick (n1 + n2, id), b', id')
      | _ -> if n1 = 0 then b else PSeq (a, b, gid ())
      end
    | _ ->
      begin match b with
      | PTick (0, _) -> a
      | _ -> PSeq (a, b, gid ())
      end
  in

  let rec slice_list
  : 'a. ('a -> prog) -> 'a list -> prog = fun f l ->
    List.fold_right
      (fun a b -> seq (f a) b) l (PTick (0, gid ()))

  and slice_block b = slice_list slice_stmt b.bstmts

  and slice_stmt s =
    let pay c p = PSeq (PTick (c, gid ()), p, gid ()) in
    match s.skind with

    | Instr il ->
      let slice_instr = function
        | Set (lv, exp, loc) ->
          let pay = pay (cost OpSet + cost (OpExp exp)) in
          begin match
            check_lvalue loc lv
          with
          | Some v -> pay (transl_set gid v exp)
          | None -> pay (PTick (0, gid ()))
          end
        | Call (None, Lval (Var fassert, NoOffset), [exp], _)
        when fassert.vname = "assert" ->
          PAssert (transl_cond exp, gid ())
        | Call (_, _, _, loc)
        | Asm (_, _, _, _, _, loc) -> E.s (
            E.error "%s:%d unsupported instruction"
              loc.file loc.line
          )
      in slice_list slice_instr il

    | Return (expo, loc) ->
      pay (cost OpReturn) (PBreak (gid ())) (* XXX *)

    | Goto (_, loc)
    | ComputedGoto (_, loc) -> E.s (
        E.error "%s:%d unsupported goto"
          loc.file loc.line
      )

    | Break _ ->
      pay (cost OpBreak) (PBreak (gid ()))

    | Continue loc -> E.s (
        E.error "%s:%d unsupported continue"
          loc.file loc.line
      )

    | If (exp, b1, b2, loc) ->
      PIf
        ( transl_cond exp
        , slice_block b1
        , slice_block b2
        , gid ()
        )

    | Switch (_, _, _, loc) -> E.s (
        E.error "%s:%d unsupported switch"
          loc.file loc.line
      )

    | Loop (b, _, _, _) ->
      let true_cond =
        let z = LVar (VNum 0) in
        CTest (z, CLe, z) in
      PWhile
        ( true_cond
        , pay (cost OpLoop) (slice_block b)
        , gid ()
        )

    | Block b -> slice_block b

    | TryFinally (_, _, loc)
    | TryExcept (_, _, _, loc) -> E.s (
        E.error "%s:%d unsupported try"
          loc.file loc.line
      )
  in
  let fmain =
    let rec f = function
      | GFun ({svar;_} as fmain, _) :: _
      when svar.vname = "main" -> fmain
      | _ :: tl -> f tl
      | [] -> E.s (
          E.error "%s: missing main function" fileName
        )
    in f globals
  in
  assert (List.for_all (fun v -> v.vglob = false) fmain.sformals);
  assert (List.for_all (fun v -> v.vglob = false) fmain.slocals);
  slice_block fmain.sbody


let _ =
  (* if Array.length Sys.argv > 2 && Sys.argv.(1) = "-tcee" then *)
  let file = Frontc.parse Sys.argv.(1) () in
  let prog = slice (fun _ -> 1) file in
  print_string "Sliced program:\n*******\n";
  pp_prog prog;
  let l = Hood.create_logctx prog in
  print_string "\nAnalysis:\n";
  Hood.analyze l Eval.tick_metric prog
