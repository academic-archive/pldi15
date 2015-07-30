type id = string

module IdMap = Map.Make(struct type t = id let compare = compare end)

type next =
  | NBlocks of int list
  | NReturn of Ast.var

type inst =
  | ITick   of int
  | IAssert of Ast.cond
  | IInc    of id * Ast.op * Ast.var
  | ISet    of id * Ast.var option
  | ICall   of Ast.var list * func ref * Ast.var option

and block =
  { bpreds: int list
  ; binsts: inst list
  ; bnexts: next
  }

and func =
  { fname : id
  ; fargs: id list
  ; flocs: id list
  ; fblks: block array
  }

let of_func: 'a Ast.func -> func =

  let blocks p =
    let open Ast in
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
    let tac: inst -> int -> int =
      fun ins id ->
        assert(IMap.mem id !m);
        let (l,n) = IMap.find id !m in
        m := IMap.add id (ins::l,n) !m;
        id in
    let rec tr p brki seqi =
      match p with
      | PTick (n,_) ->    tac (ITick (n)) seqi
      | PInc (i,o,v,_) -> tac (IInc (i,o,v)) seqi
      | PSet (i,vo,_) ->  tac (ISet (i,vo)) seqi
      | PAssert (c,_) ->  tac (IAssert (c)) seqi
      | PBreak (_) ->     brki
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
    let endi = tr (PReturn (VNum 0,())) (-1) (-1) in
    let entry = tr p endi endi in
    let a = Array.make !n (Obj.magic 0) in
    IMap.iter (fun k v ->
      let (l,n) = IMap.find k !m in
      a.(k) <- { bpreds = []; binsts = l; bnexts = n }
    ) !m;
    (a, entry) in

  let rpo (a, entry) =
    let n = ref (Array.length a) in
    let b = Array.make !n (Obj.magic 0) in
    let rec f i =
      begin match a.(i).bnexts with
      | NReturn _ -> ()
      | NBlocks bs -> List.iter f bs
      end;
      decr n;
      b.(!n) <- a.(i);
    in
    f entry; b
  in

  let preds a =
    let p = Array.make (Array.length a) [] in
    let addp b i = p.(i) <- b :: p.(i) in
    for n = 0 to Array.length a - 1 do
      match a.(n).bnexts with
      | NReturn _ -> ()
      | NBlocks bs -> List.iter (addp n) bs
    done;
    Array.mapi (fun i b ->
      { b with bpreds = p.(i) }
    ) a
  in

  fun f ->
    { fname = f.Ast.fname
    ; fargs = f.Ast.fargs
    ; flocs = f.Ast.flocs
    ; fblks = blocks f.Ast.fbody |> rpo |> preds
    }
