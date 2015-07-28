type var = string

type inst =
  | Const of int
  | Add of var * var
  | Sub of var * var
  | Call of fprog ref * var list

and block =
  { preds: int list
  ; insts: inst list
  ; nexts: int list
  }

and fprog =
  { inputs: var list
  ; blocks: block array
  }


open Ast

(* JAN: insert code here *)
