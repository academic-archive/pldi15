
open Ast

type nexts = NBlocks of int list
	     | NReturn of var

type inst =
  | ITick   of int
  | IAssert of cond
  | IInc    of id * op * var
  | ISet    of id * var option
  | ICall of var list * cfun ref * var option

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

let of_prog : int IdMap.t -> 'a func -> cfun =

  fun fidmap astFun ->

    let counter = ref (-1) in

    let fresh_int _ =
      counter := !counter + 1;
      !counter
    in

    let cont_return var insts =
      let n = fresh_int () in
      (n, { bPreds = []
	  ; bInsts = insts
	  ; bNexts = NReturn var
	  }
      )
    in

    let cont_break_init _ = failwith "Not in a loop." in

    let cont_end_init _ = failwith "Missing return statement." in

    let constraints = ref [] in

    let add_constr n m =
      constraints := (n,m) :: !constraints
    in

    let rec mkblocks cont_break cont_end prog =
      match prog with
    	| PTick (n,_) ->
	  ((fun insts -> cont_end (List.append insts [ITick n]) ), [])
	| PAssert (cond,_) ->
	  ((fun insts -> cont_end (List.append insts [IAssert cond]) ), [])
    	| PInc (id,op,var,_) ->
	  ((fun insts -> cont_end (List.append insts [IInc (id,op,var)]) ), [])
    	| PSet (id,ovar,_) ->
	  ((fun insts -> cont_end (List.append insts [ISet (id,ovar)]) ), [])
	| PCall (oid,id,vars,_) ->
	  (*ICall of var list * cfun ref * var option*) failwith "function calls not implemented"
    	| PBreak _ ->
	  (cont_break, [])
    	| PReturn (v,_) ->
	  (cont_return v, [])
    	| PLoop (p,_) ->
	  let loop_entry = fresh_int () in
	  let cont_loop insts =
	    let n = fresh_int () in
	    let newblock =
	      { bPreds = []
	      ; bInsts = insts
	      ; bNexts = NBlocks [loop_entry]
	      }
	    in
	    (n,newblock)
	  in
	  let (loop_cont, blocks) = mkblocks cont_end cont_loop p in
	  let (n_loop, block_loop) = loop_cont [] in
	  let _ = add_constr n_loop loop_entry in
	  (cont_loop,(n_loop,block_loop)::blocks)
	    
    	| PIf (cond, pif, pelse, _) ->
	  let (cont_if,blocks_if) = mkblocks cont_break cont_end pif in
	  let (cont_else,blocks_else) = mkblocks cont_break cont_end pelse in
	  let (n_if,block_if) = cont_if [] in
	  let (n_else,block_else) = cont_else [] in
	  let blocks =
	    let x = (n_if,block_if)::blocks_if in
	    let y = (n_else,block_else)::blocks_else in
	    List.append x y
	  in
	  let cont insts =
	    let n = fresh_int () in
	    ( n,
	      { bPreds = []
	      ; bInsts = insts
	      ; bNexts = NBlocks [n_if;n_else]
	      }
	    )
	  in
	  (cont,blocks)

    	| PSeq (p1,p2,_) ->
	  let (cont_end',blocks2) = mkblocks cont_break cont_end p2 in
	  let (cont_end'',blocks1) = mkblocks cont_break cont_end' p1 in
	  (cont_end'',List.append blocks1 blocks2) 
    in
    
    let blocklist =
      let (cont,blocks) = mkblocks cont_break_init cont_end_init astFun.fbody in
      (cont [])::blocks
    in
    let blocks = failwith "" in
    { fName = astFun.fname
    ; fArgs = astFun.fargs
    ; fLocals = astFun.flocs
    ; fBlocks = blocks
    }

