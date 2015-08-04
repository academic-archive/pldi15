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
      let i = incr n; !n-1 in
      m := IMap.add i ([],nxt) !m;
      i in
    let tac ins id =
      assert(IMap.mem id !m);
      let (l,n) = IMap.find id !m in
      m := IMap.add id (ins::l,n) !m;
      id in
    let rec tr p brki seqi =
      match p with
      | PTick (n,_) ->
        if n=0 then seqi else tac (ITick (n)) seqi
      | PInc (i,o,v,_) -> tac (IInc (i,o,v)) seqi
      | PSet (i,vo,_) ->  tac (ISet (i,vo)) seqi
      | PAssert (c,_) ->  tac (IAssert (c)) seqi
      | PBreak (_) ->     nuw (JJmp [brki])
      | PReturn (v,_) ->  nuw (JRet (v))
      | PIf (c,a,b,_) ->
        let ida = tr a brki (nuw (JJmp [seqi])) in
        let idb = tr b brki (nuw (JJmp [seqi])) in
        let ida = tac (IAssert (c)) ida in
        let idb = tac (IAssert (cond_neg c)) idb in
        nuw (JJmp [ida; idb])
      | PLoop (a,_) ->
        let lid = nuw (JJmp []) in
        let aid = tr a seqi lid in
        let (l,_) = IMap.find lid !m in
        m := IMap.add lid (l, JJmp [aid]) !m;
        aid
      | PSeq (a,b,_) ->
        tr a brki (tr b brki seqi)
    in
    let endi = nuw (JRet (VNum 0)) in
    let entry = tr p endi endi in
    let a = Array.make !n (Obj.magic 0) in
    IMap.iter (fun k (l,n) ->
      a.(k) <- { bpreds = []; binsts = l; bjump = n }
    ) !m;
    (a, entry) in

  let merge a =
    let rec dst f t =
      if t < f then t else
      match a.(t).bjump with
      | JJmp [x] -> dst t x
      | _ -> t in
    let chg = ref true in
    while !chg do
      chg := false;
      for n=0 to Array.length a - 1 do
        let b = a.(n) in
        match b.bjump with
        | JJmp [n'] ->
          let s = a.(n') in
          if s.bpreds = [n] then begin
            a.(n) <-
              { bpreds = b.bpreds
              ; binsts = b.binsts @ s.binsts
              ; bjump =
                match s.bjump with
                | JJmp l -> JJmp (List.map (dst n) l)
                | j -> j
              };
            chg := true;
          end
        | _ -> ()
      done;
    done;
    a in

  let rpo entry a =
    let n = ref (Array.length a) in
    let b = Array.make !n (Obj.magic 0) in
    let r = Array.make !n (-1) in
    let rec f i =
      if r.(i) < 0 then begin
        r.(i) <- 0;
        begin match a.(i).bjump with
        | JJmp bs -> List.iter f bs
        | JRet _ -> ()
        end;
        decr n;
        r.(i) <- !n;
        b.(!n) <- a.(i);
      end
    in
    f entry;
    Array.sub b !n (Array.length b - !n) |>
    Array.map (fun b ->
      let bjump =
          match b.bjump with
          | JJmp l ->
            JJmp (List.map (fun i -> r.(i) - !n) l)
          | n -> n in
      { b with bjump }
    )
  in

  let preds a =
    let p = Array.make (Array.length a) [] in
    let addp b i = p.(i) <- b :: p.(i) in
    addp (-1) 0; (* the start block gets an extra predecessor *)
    for n = 0 to Array.length a - 1 do
      match a.(n).bjump with
      | JRet _ -> ()
      | JJmp bs -> List.iter (addp n) bs
    done;
    Array.mapi (fun i b ->
      { b with bpreds = p.(i) }
    ) a
  in

  fun f ->
    { fname = f.fname
    ; fargs = f.fargs
    ; flocs = f.flocs
    ; fbody = blocks f.fbody
           |> (fun (a,e) -> rpo e a)
           |> preds
           |> merge
           |> rpo 0
           |> preds
    }


let pp_func {fname; fargs; flocs; fbody} =
  let open Printf in
  let pp_var = Parse.pp_var in

  let rec pp_list p oc = function
    | [x] -> fprintf oc "%a" p x
    | x :: xs -> fprintf oc "%a, %a" p x (pp_list p) xs
    | [] -> () in
  let pp_b oc n =
    if n = -1 then fprintf oc "start"
              else fprintf oc "b%d" n in

  let rec lsum prns = function
    | LAdd (l1, l2) ->
      if prns then printf "(";
      lsum false l1; printf " + "; lsum false l2;
      if prns then printf ")"
    | LSub (l1, l2) ->
      if prns then printf "(";
      lsum false l1; printf " - "; lsum true l2;
      if prns then printf ")"
    | LMult (k, l) ->
      printf "%d * " k;
      lsum true l
    | LVar v ->
      printf "%a" pp_var v in

  let cond = function
    | CTest (l1, cmp, l2) ->
      lsum false l1;
      printf " %s " (
        match cmp with
        | CLe -> "<="
        | CGe -> ">="
        | CLt -> "<"
        | CGt -> ">"
      );
      lsum false l2
    | CNonDet -> printf "*" in

  Array.iteri (fun i {binsts=is; bjump; bpreds=ps} ->
    printf "\nb%d: # preds: %a \n" i (pp_list pp_b) ps;
    List.iter (function
      | ITick n -> printf "\ttick %d\n" n
      | IAssert c -> printf "\tassert "; cond c; printf "\n"
      | IInc (id, o, v) ->
        let op = match o with OPlus -> "+" | OMinus -> "-" in
        printf "\t%s %s= %a\n" id op pp_var v
      | ISet (id, Some v) -> printf "\t%s = %a\n" id pp_var v
      | ISet (id, None) -> printf "\t%s = *\n" id
      | ICall _ -> failwith "pp_func, no call supported"
    ) is;
    match bjump with
    | JJmp l -> printf "\tgoto %a\n" (pp_list pp_b) l
    | JRet v -> printf "\tret %a\n" pp_var v
  ) fbody


let _ =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "-tcfg" then
    let (_,f) = Parse.pa_file stdin in
    let cf = of_func {fname="main"; fargs=[]; flocs=[]; fbody=f} in
    pp_func cf
