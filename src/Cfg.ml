
open Ast

type nexts = NBlocks of int list
	     | NReturn of var

type inst =
  | ITick   of int
  | IAssert of cond
  | IInc    of id * op * var
  | ISet    of id * var option
  | Call of var list * cfun ref * var option

and block =
  { bPreds: int list
  ; bInsts: inst list
  ; bNexts: nexts
  }

and cfun =
    { fName : id
    ; fArgs: id list
    ; fLocals: id list
    ; fBlocks: block array
    }



module IdMap = Map.Make(struct type t = id let compare = compare end)

