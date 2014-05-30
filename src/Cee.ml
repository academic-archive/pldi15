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

(* simplify assignments *)
let transl_set gid v exp =

  let swtch = function
    | OPlus -> OMinus
    | OMinus -> OPlus in

  let combine (v1, l1) (v2, l2) =
    begin match v1, v2 with
    | Some e, None
    | None, Some e ->
      (None, e :: l1 @ l2)
    | Some e1, Some e2 ->
      (Some e1, e2 :: l1 @ l2)
    | None, None ->
      failwith "non linear assignment"
    end in

  let rec f o = function
    | LVar (VNum n) -> (Some (o, VNum n), [])
    | LVar (VId v') ->
      if v' = v
        then (assert (o = OPlus); (None, []))
        else (Some (o, VId v'), [])
    | LAdd (e1, e2) -> combine (f o e1) (f o e2)
    | LSub (e1, e2) -> combine (f o e1) (f (swtch o) e2)
    | LMult (-1, e) -> f (swtch o) e
    | LMult (k, e) ->
      failwith "multiplication by constants not implemented"

  in try
    let init, l = f OPlus (transl_sum exp) in

    let p = List.fold_right
      (fun (op, v') a ->
        PSeq (PInc (v, op, v', gid ()), a, gid ()))
      l (PTick (0, gid ())) in

    match init with
    | Some (OPlus, v') ->
      PSeq (PSet (v, Some v', gid ()), p, gid ())
    | Some (OMinus, v') ->
      PSeq (PSet (v, Some (VNum 0), gid ()),
      PSeq (PInc (v, OMinus, v', gid ()),
        p, gid ()), gid ())
    | None -> p

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
