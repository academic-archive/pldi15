(* Global types *)


type id = string
type var = VId of id | VNum of int
type op = OPlus | OMinus

type comp = CLe | CGe | CLt | CGt
type lsum =
  | LAdd of lsum * lsum
  | LSub of lsum * lsum
  | LMult of int * lsum
  | LVar of var

type cond = CTest of lsum * comp * lsum | CNonDet

let cond_neg = function
  | CTest (a, op, b) ->
    let nl = [CLe, CGt; CGe, CLt; CLt, CGe; CGt, CLe]
    in CTest (a, List.assoc op nl, b)
  | CNonDet -> CNonDet


(* AST definition of while programs *)

type 'a prog =
  | PTick   of int * 'a
  | PBreak  of 'a
  | PReturn of var * 'a
  | PAssert of cond * 'a
  | PInc    of id * op * var * 'a
  | PSet    of id * var option * 'a
  | PCall   of id option * id * var list * 'a
  | PLoop   of 'a prog * 'a
  | PIf     of cond * 'a prog * 'a prog * 'a
  | PSeq    of 'a prog * 'a prog * 'a

let prog_data = function
  | PTick (_, a)
  | PBreak a
  | PReturn (_, a)
  | PAssert (_, a)
  | PInc (_, _, _, a)
  | PSet (_, _, a)
  | PCall (_, _, _, a)
  | PLoop (_, a)
  | PIf (_, _, _, a)
  | PSeq (_, _, a) -> a

module Mk = struct
  let rec seq a b =
    match a with
    | PSeq (a1, a2, _) ->
      seq a1 (seq a2 b)
    | PTick (0, _) -> b
    | _ ->
      begin match b with
      | PTick (0, _) -> a
      | _ -> PSeq (a, b, ())
      end
end


(* Control flow graphs for while programs *)

type jump =
  | JList of int list
  | JRet of var

type inst =
  | ITick   of int
  | IAssert of cond
  | IInc    of id * op * var
  | ISet    of id * var option
  | ICall   of id option * id * var list

type block =
  { bpreds: int list
  ; binsts: inst list
  ; bjump: jump
  }


(* Functions *)

type 'a func =
  { fname: id
  ; fargs: id list
  ; flocs: id list
  ; fbody: 'a
  }

type 'a cfg_func = block array func
type 'a ast_func = 'a prog func
