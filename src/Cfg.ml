open Ast

let of_func: 'a ast_func -> 'a cfg_func =

  let blocks p =
    let open Ast in
    let module IMap = Map.Make(
      struct
        type t = int
        let compare = compare
      end
    ) in
    let n = ref 0 in
    let m = ref IMap.empty in
    let nuw nxt =
      incr n;
      m := IMap.add !n ([],nxt) !m;
      !n in
    let tac ins id =
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
      | PBreak (_) ->     nuw (JList [brki])
      | PReturn (v,_) ->  nuw (JRet (v))
      | PIf (c,a,b,_) ->
        let ida = tr a brki seqi in
        let idb = tr b brki seqi in
        nuw (JList [ida; idb])
      | PLoop (a,_) ->
        let lid = nuw (JList []) in
        let aid = tr a seqi lid in
        let (l,_) = IMap.find lid !m in
        m := IMap.add lid (l, JList [aid]) !m;
        lid
      | PSeq (a,b,_) ->
        tr a brki (tr b brki seqi)
    in
    let endi = nuw (JRet (VNum 0)) in
    let entry = tr p endi endi in
    let a = Array.make !n (Obj.magic 0) in
    IMap.iter (fun k v ->
      let (l,n) = IMap.find k !m in
      a.(k) <- { bpreds = []; binsts = l; bjump = n }
    ) !m;
    (a, entry) in

  let rpo (a, entry) =
    let n = ref (Array.length a) in
    let b = Array.make !n (Obj.magic 0) in
    let r = Array.make !n 0 in
    let rec f i =
      begin match a.(i).bjump with
      | JRet _ -> ()
      | JList bs -> List.iter f bs
      end;
      decr n;
      r.(i) <- !n;
      b.(!n) <- a.(i);
    in
    f entry;
    Array.mapi (fun i b ->
      let bjump =
          match b.bjump with
          | JList l ->
            JList (List.map (fun i -> r.(i)) l)
          | n -> n in
      { b with bjump }
    ) b
  in

  let preds a =
    let p = Array.make (Array.length a) [] in
    let addp b i = p.(i) <- b :: p.(i) in
    for n = 0 to Array.length a - 1 do
      match a.(n).bjump with
      | JRet _ -> ()
      | JList bs -> List.iter (addp n) bs
    done;
    Array.mapi (fun i b ->
      { b with bpreds = p.(i) }
    ) a
  in

  fun f ->
    { fname = f.fname
    ; fargs = f.fargs
    ; flocs = f.flocs
    ; fbody = blocks f.fbody |> rpo |> preds
    }
