open Ast

module IdMap = Map.Make(struct type t = id let compare = compare end)

type next =
  | NBlocks of int list
  | NReturn of var

type inst =
  | ITick   of int
  | IAssert of cond
  | IInc    of id * op * var
  | ISet    of id * var option
  | ICall   of var list * cfun ref * var option

and block =
  { bPreds: int list
  ; bInsts: inst list
  ; bNexts: next
  }

and cfun =
  { fName : id
  ; fArgs: id list
  ; fLocals: id list
  ; fBlocks: block array
  }

let tr_prog: unit prog -> (block array * int) =

  let module IMap = Map.Make(
    struct
      type t = int
      let compare = compare
    end
  ) in

  let n: int ref = ref 0 in
  let id: unit -> int =
    fun () -> incr n; !n in

  let m: (inst list * next) IMap.t ref =
    ref IMap.empty in

  let add: int -> (inst list * next) -> unit =
    fun id ln ->
      assert(not (IMap.mem id !m));
      m := IMap.add id ln !m in

  let tac: inst -> int -> unit =
    fun ins id ->
      assert(IMap.mem id !m);
      let (l,n) = IMap.find id !m in
      m := IMap.add id (ins::l,n) !m in

  let rec tr p brki seqi =
    match p with
    | PTick (n,_) ->
      tac (ITick (n)) seqi;
      seqi
    | PInc (i,o,v,_) ->
      tac (IInc (i,o,v)) seqi;
      seqi
    | PSet (i,vo,_) ->
      tac (ISet (i,vo)) seqi;
      seqi
    | PBreak (_) ->
      brki
    | PReturn (v,_) ->
      let reti = id () in
      add reti ([], NReturn (v));
      reti
    | PIf (c,a,b,_) ->
      let ida = tr a brki seqi in
      let idb = tr b brki seqi in
      let ifi = id () in
      add ifi ([], NBlocks [ida; idb]);
      ifi
    | PLoop (a,_) ->
      let lid = id () in
      add lid ([], NBlocks []);
      let aid = tr a seqi lid in
      let (l,_) = IMap.find lid !m in
      m := IMap.add lid (l, NBlocks [aid]) !m;
      lid
    | PSeq (a,b,_) ->
      let bid = tr b brki seqi in
      let aid = tr a brki bid in
      aid
    in

    fun p ->
      let entry = tr p (-1) (-1) in
      let a = Array.make !n {bPreds = []; bInsts = []; bNexts = NBlocks []} in
      IMap.fold (fun k v () ->
        let (l,n) = IMap.find k !m in
        a.(k) <-
          { bPreds = []
          ; bInsts = l
          ; bNexts = n
          }
      ) !m ();
      (a, entry)
