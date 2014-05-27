(* Slicing and normalizing CIL programs *)
open Cil
open Parse
module E = Errormsg


(* test if [v] must be tracked in the analysis *)
let is_tracked v =
  v.vglob = false && isIntegralType v.vtype

(* simplify assignments *)
let transl_set gid v exp =

  let module Fail = struct exception E end in

  let swtch = function
    | OPlus -> OMinus
    | OMinus -> OPlus in

  let rec f o = function
    | Const (CInt64 (i, _, _)) ->
      (Some (o, VNum (Int64.to_int i)), [])

    | Const (CChr c) ->
      f o (Const (charConstToInt c))

    | Lval (Var vi, NoOffset)
    when is_tracked vi ->
      if vi.vname = v
        then (assert (o = OPlus); (None, []))
        else (Some (o, VId vi.vname), [])

    | UnOp (Neg, e, _) -> f (swtch o) e

    | BinOp ((PlusA | MinusA) as op, e1, e2, _) ->
      let v1, l1 = f o e1 in
      let o' = if op = PlusA then o else swtch o in
      let v2, l2 = f o' e2 in
      begin match v1, v2 with
      | Some e, None
      | None, Some e ->
        (None, e :: l1 @ l2)
      | Some e1, Some e2 ->
        (Some e1, e2 :: l1 @ l2)
      | None, None ->
        failwith "non linear assignment"
      end

    | BinOp (Mult, e, Const (CInt64 (i, _, _)), _)
    | BinOp (Mult, Const (CInt64 (i, _, _)), e, _) ->
      failwith "multiplication by constants not implemented"

    | _ -> raise Fail.E

  in try
    let init, l = f OPlus exp in

    let p = List.fold_right
      (fun (op, v') a ->
        PSeq (PInc (v, op, v', gid ()), a, gid ()))
      l (PSkip (gid ())) in

    match init with
    | Some (OPlus, v') ->
      PSeq (PSet (v, v', gid ()), p, gid ())
    | Some (OMinus, v') ->
      PSeq (PSet (v, VNum 0, gid ()),
      PSeq (PInc (v, OMinus, v', gid ()),
        p, gid ()), gid ())
    | None -> p

  with Fail.E -> PSkip (gid ()) (* XXX use 'x = *' *)


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

  let rec slice_list: 'a. ('a -> prog) -> 'a list -> prog =
  fun f l ->
    let rec seq a b =
      match a with
      | PSeq (a1, a2, id) ->
        PSeq (a1, (seq a2 b), id)
      | PSkip _ -> b
      | _ -> PSeq (a, b, gid ()) in
    List.fold_right
      (fun a b -> seq (f a) b) l
      (PSkip (gid ()))

  and slice_block b =
    slice_list slice_stmt b.bstmts

  and slice_stmt s =
    match s.skind with

    | Instr il ->
      let slice_instr = function
        | Set (lv, exp, loc) ->
          begin match
            check_lvalue loc lv
          with
          | Some v -> transl_set gid v exp
          | None -> PSkip (gid ())
          end
        | Call (_, _, _, loc)
        | Asm (_, _, _, _, _, loc) -> E.s (
            E.error "%s:%d unsupported instruction"
              loc.file loc.line
          )
      in slice_list slice_instr il

    | Return (expo, loc) -> PBreak (gid ()) (* XXX *)

    | Goto (_, loc)
    | ComputedGoto (_, loc) -> E.s (
        E.error "%s:%d unsupported goto"
          loc.file loc.line
      )

    | Break _ -> PBreak (gid ())

    | Continue loc -> E.s (
        E.error "%s:%d unsupported continue"
          loc.file loc.line
      )

    | If (exp, b1, b2, loc) -> failwith "if not implemented"

    | Switch (_, _, _, loc) -> E.s (
        E.error "%s:%d unsupported switch"
          loc.file loc.line
      )

    | Loop (b, _, _, _) -> failwith "loop not implemented"

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
  pp_prog (slice (fun _ -> 0) file)
