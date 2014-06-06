(* Parsing and definition of programs *)
exception SyntaxError of string

(* lexing *)

type token =
  | TAssert | TWhile | TIf | TElse | TBreak
  | TSemi | TComma | TPlus | TMinus | TStar
  | TLParen | TRParen
  | TLt | TGt | TLe | TGe | TEq
  | TFunc | TLocal | TReturn
  | TIdnt of string
  | TNum of int
  | TEof

let mk_lexer ic =

  let (next, back) =
    let mem = ref None in
    (fun () ->
      match !mem with
      | None -> (try input_char ic with End_of_file -> '\xff')
      | Some c -> (mem := None; c)),
    (fun c -> mem := Some c) in

  let isalpha = function
    | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
    | _ -> false in

  let rec getstr s =
    let c = next () in
    if isalpha c
      then getstr (s ^ String.make 1 c)
      else (back c; s) in

  let digit c = Char.code c - 48 in

  let rec getnum n =
    match next () with
    | ('0' .. '9') as c -> getnum (10 * n + digit c)
    | c -> (back c; n) in

  let rec f () =
    match next () with
    | c when isalpha c ->
      let s = getstr (String.make 1 c) in
      if s = "while" then TWhile
      else if s = "assert" then TAssert
      else if s = "if" then TIf
      else if s = "else" then TElse
      else if s = "break" then TBreak
      else if s = "func" then TFunc
      else if s = "local" then TLocal
      else if s = "return" then TReturn
      else TIdnt s
    | ('0' .. '9') as c -> TNum (getnum (digit c))
    | ';' -> TSemi | ',' -> TComma
    | '+' -> TPlus | '-' -> TMinus | '*' -> TStar
    | '(' -> TLParen | ')' -> TRParen
    | '<' -> (match next () with '=' -> TLe | c -> back c; TLt)
    | '>' -> (match next () with '=' -> TGe | c -> back c; TGt)
    | '=' -> TEq
    | '\xff' -> TEof
    | ' ' | '\t' | '\r' | '\n' -> f ()
    | _ -> raise (SyntaxError "lexing")

  in f

let string_of_token = function
  | TAssert -> "ASSERT"
  | TWhile -> "WHILE" | TBreak -> "BREAK"
  | TIf -> "IF" | TElse -> "ELSE"
  | TIdnt id -> Printf.sprintf "IDNT %S" id
  | TNum n -> Printf.sprintf "NUM %d" n
  | TSemi -> "SEMI" | TComma -> "COMMA"
  | TStar -> "STAR" | TPlus -> "PLUS" | TMinus -> "MINUS"
  | TLParen -> "LPAREN" | TRParen -> "RPAREN"
  | TLt -> "LT" | TGt -> "GT"
  | TLe -> "LE" | TGe -> "GE"
  | TEq -> "EQ"
  | TFunc -> "FUNC" | TLocal -> "LOCAL"
  | TReturn -> "RETURN"
  | TEof -> "EOF"


(* parsing *)

type stream_strict = SEof | STok of token * stream
and stream = stream_strict lazy_t

let rec stream_of_fun f = lazy (
  match f () with
  | TEof -> SEof
  | tok -> STok (tok, stream_of_fun f)
)

(* unique identifiers are used to mark each node of the AST *)
type uid = int

type 'a pm = uid * stream -> 'a option * (uid * stream)
let ret x = fun s -> (Some x, s)
let reti f = fun (i, s) -> (Some (f i), (i + 1, s))
let bnd x f s =
  match x s with
  | (None, _) -> (None, s)
  | (Some vx, s') -> f vx s'

let rec p_or = function
  | p :: pl -> fun s ->
    begin match p s with
    | (None, _) -> p_or pl s
    | res -> res
    end
  | [] -> fun s -> (None, s)

let p_tok f (i, s) =
  match Lazy.force s with
  | STok (tok, s') ->
    begin match f tok with
    | None -> (None, (i, s))
    | Some x -> (Some x, (i, s'))
    end
  | _ -> (None, (i, s))


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
  | CTest (a, CLe, b) -> CTest (a, CGt, b)
  | CTest (a, CGe, b) -> CTest (a, CLt, b)
  | CTest (a, CLt, b) -> CTest (a, CGe, b)
  | CTest (a, CGt, b) -> CTest (a, CLe, b)
  | CNonDet -> CNonDet

type prog =
  | PTick of int * uid
  | PBreak of uid
  | PReturn of var * uid
  | PAssert of cond * uid
  | PInc of id * op * var * uid
  | PSet of id * var option * uid
  | PCall of id option * id * var list * uid
  | PWhile of cond * prog * uid
  | PIf of cond * prog * prog * uid
  | PSeq of prog * prog * uid

type func =
  { fname: id
  ; fargs: id list
  ; flocs: id list
  ; fbody: prog
  }

(* parser for one file *)
let p_file: (func list * prog) pm =

  let is t t' = if t = t' then Some () else None in
  let num = function TNum n -> Some n | _ -> None in
  let idnt = function TIdnt id -> Some id | _ -> None in
  let binop = function
    | TPlus -> Some OPlus
    | TMinus -> Some OMinus
    | _ -> None in

  let p_num = p_or
    [ bnd (p_tok (is TMinus)) (fun () ->
      bnd (p_tok num) (fun k ->
        ret (-k)
      ))
    ; p_tok num
    ] in

  let p_var = p_or
    [ bnd (p_tok idnt) (fun id -> ret (VId id))
    ; bnd p_num (fun n -> ret (VNum n))
    ] in

  let p_parens p =
    bnd (p_tok (is TLParen)) (fun () ->
    bnd p (fun x ->
    bnd (p_tok (is TRParen)) (fun () ->
      ret x
    ))) in

  let rec p_term () = p_or

    (* variable *)
    [ bnd (p_tok idnt) (fun id ->
        ret (LVar (VId id))
      )

    (* constant or multiplication *)
    ; bnd p_num (fun k -> p_or
        [ bnd (p_tok (is TStar)) (fun () ->
          bnd (p_term ()) (fun l ->
            ret (LMult (k, l))
          ))
        ; ret (LVar (VNum k))
        ]
      )

    (* parenthesized expressions *)
    ; p_parens (fun x -> p_lsum () x)
    ]

  and p_sum () =
    bnd (p_term ()) (fun lhs -> p_or

      (* addition *)
      [ bnd (p_tok (is TPlus)) (fun () ->
        bnd (p_sum ()) (fun rhs ->
          ret ((lhs, true) :: rhs)
        ))

      (* substraction *)
      ; bnd (p_tok (is TMinus)) (fun () ->
        bnd (p_sum ()) (fun rhs ->
          ret ((lhs, false) :: rhs)
        ))

      (* simple term *)
      ; ret [(lhs, true)]
      ]
    )

  and p_lsum () =
    bnd (p_sum ()) (fun s ->
      let f (l, toadd) (l', toadd') =
        if toadd
          then (LAdd (l, l'), toadd')
          else (LSub (l, l'), toadd') in
      ret (fst (List.fold_left f (List.hd s) (List.tl s)))
    ) in

  let p_cond () = p_or
    [ bnd (p_tok (is TStar)) (fun () ->
        ret CNonDet
      )
    ; let comp = function
        | TLe -> Some CLe
        | TGe -> Some CGe
        | TLt -> Some CLt
        | TGt -> Some CGt
        | _ -> None in
      bnd (p_lsum ()) (fun left ->
      bnd (p_tok comp) (fun c ->
      bnd (p_lsum ()) (fun right ->
        ret (CTest (left, c, right))
      )))
    ] in

  let rec p_list p = p_or
    [ bnd p (fun id ->
      bnd (p_tok (is TComma)) (fun () ->
      bnd (p_list p) (fun ids ->
        ret (id :: ids)
      )))
    ; bnd p (fun id -> ret [id])
    ; ret []
    ] in

  let rec p_atomic () = p_or

    (* Increment/Decrement, PInc *)
    [ bnd (p_tok idnt) (fun id ->
      bnd (p_tok (is TEq)) (fun () ->
      bnd (p_tok (is (TIdnt id))) (fun () ->
      bnd (p_tok binop) (fun op ->
      bnd p_var (fun v ->
        reti (fun i -> PInc (id, op, v, i))
      )))))

    (* Function call, PCall *)
    ; bnd (p_or
        [ bnd (p_tok idnt) (fun r ->
          bnd (p_tok (is TEq)) (fun () ->
            ret (Some r)
          ))
        ; ret None
        ]
      ) (fun ro ->
      bnd (p_tok idnt) (fun fname ->
      bnd (p_parens (p_list p_var)) (fun args ->
        reti (fun i -> PCall (ro, fname, args, i))
      )))

    (* Assignment, PSet *)
    ; bnd (p_tok idnt) (fun id ->
      bnd (p_tok (is TEq)) (fun () ->
      bnd (p_or
        [ bnd p_var (fun v -> ret (Some v))
        ; bnd (p_tok (is TStar)) (fun () -> ret None)
        ]
      ) (fun vo ->
        reti (fun i -> PSet (id, vo, i))
      )))

    (* Tick, PTick *)
    ; bnd (p_parens (p_or [p_num; ret 0])) (fun n ->
        reti (fun i -> PTick (n, i))
      )

    (* Break, PBreak *)
    ; bnd (p_tok (is TBreak)) (fun () ->
        reti (fun i -> PBreak i)
      )

    (* Return, PReturn *)
    ; bnd (p_tok (is TReturn)) (fun () ->
      bnd p_var (fun v ->
        reti (fun i -> PReturn (v, i))
      ))

    (* While loop, PWhile *)
    ; bnd (p_tok (is TWhile)) (fun () ->
      bnd (p_cond ()) (fun cond ->
      bnd (p_atomic ()) (fun prog ->
        reti (fun i -> PWhile (cond, prog, i))
      )))

    (* Assertion, PAssert *)
    ; bnd (p_tok (is TAssert)) (fun () ->
      bnd (p_cond ()) (fun cond ->
        reti (fun i -> PAssert (cond, i))
      ))

    (* Conditional, PIf *)
    ; bnd (p_tok (is TIf)) (fun () ->
      bnd (p_cond ()) (fun cond ->
      bnd (p_atomic ()) (fun p1 ->
        p_or
        (* Conditional with else part *)
        [ bnd (p_tok (is TElse)) (fun () ->
          bnd (p_atomic ()) (fun p2 ->
            reti (fun i -> PIf (cond, p1, p2, i))
          ))
        (* No else part, implicit tick 0 *)
        ; bnd (reti (fun i -> PTick (0, i))) (fun p2 ->
            reti (fun i -> PIf (cond, p1, p2, i))
          )
        ]
      )))

    (* Parenthesized complex statement *)
    ; p_parens (fun x -> p_complex () x)
    ]

  and p_complex () = p_or

    (* sequence or atomic command *)
    [ bnd (p_atomic ()) (fun prog1 ->
      p_or
        [ bnd (p_tok (is TSemi)) (fun () ->
          bnd (p_complex ()) (fun prog2 ->
            reti (fun i -> PSeq (prog1, prog2, i))
          ))
        ; ret prog1
        ]
      )
    ] in

  (* List of function definitions *)
  let rec p_funcs () =

    p_or
      [ bnd (p_tok (is TFunc)) (fun () ->
        bnd (p_tok idnt) (fun fname ->
        bnd (p_parens (p_list (p_tok idnt))) (fun fargs ->
        let locs = p_or
          [ bnd (p_tok (is TLocal)) (fun () ->
              p_parens (p_list (p_tok idnt))
            )
          ; ret []
          ] in
        bnd locs (fun flocs ->
        bnd (p_atomic ()) (fun fbody ->
        bnd (p_funcs ()) (fun funcs ->
          ret ({fname; fargs; flocs; fbody} :: funcs)
        ))))))
      ; ret []
      ] in

  bnd (p_funcs ()) (fun funcs ->
  bnd (p_complex ()) (fun prog ->
  p_or
    [ bnd (p_tok (fun x -> Some (string_of_token x)))
      (fun t -> raise (SyntaxError ("unexpected token " ^ t)))
    ; ret (funcs, prog)
    ]
  ))

let pa_file ic =
  match p_file (1, stream_of_fun (mk_lexer ic)) with
  | (Some f, _) -> f
  | (None, _) -> raise (SyntaxError "parse error")
let pa_prog ic = snd (pa_file ic)

let prog_id = function
  | PTick (_, id) | PBreak id | PAssert (_, id) | PInc (_, _, _, id)
  | PSet (_, _, id) | PWhile (_, _, id) | PIf (_, _, _, id)
  | PReturn (_, id) | PCall (_, _, _, id)
  | PSeq (_, _, id) -> id


(* pretty printing *)

let pp_var oc = function
  | VNum n -> Printf.fprintf oc "%d" n
  | VId x -> Printf.fprintf oc "%s" x


let pp_file_hooks pre post (fl, prog) =
  let open Printf in

  let rec pp_list p oc = function
    | [x] -> fprintf oc "%a" p x
    | x :: xs -> fprintf oc "%a, %a" p x (pp_list p) xs
    | [] -> () in

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

  let rec idnt i =
    if i <> 0 then
      begin print_string " "; idnt (i - 1) end in

  let delta = 2 in

  let rec f lvl prns = function
    | PTick (0, _) -> printf "()"
    | PTick (n, _) -> printf "(%d)" n
    | PBreak _ -> printf "break"
    | PAssert (c, _) -> printf "assert "; cond c
    | PReturn (v, _) -> printf "return %a" pp_var v
    | PCall (xo, f, args, _) ->
      begin match xo with
      | Some x -> printf "%s = " x
      | _ -> ()
      end; printf "%s(%a)" f (pp_list pp_var) args
    | PSet (id, Some v, _) -> printf "%s = %a" id pp_var v
    | PSet (id, None, _) -> printf "%s = *" id
    | PInc (id, o, v, _) ->
      let op = match o with OPlus -> "+" | OMinus -> "-" in
      printf "%s = %s %s %a" id id op pp_var v
    | PSeq (p1,  p2, _) ->
      let lvl' = if prns
        then (idnt lvl; printf "(\n"; lvl + delta)
        else lvl in
      g lvl' true p1; printf ";\n";
      g lvl' false p2;
      if prns then (printf "\n"; idnt lvl; printf ")")
    | PIf (c, p1, p2, _) ->
      printf "if "; cond c; printf "\n";
      g (lvl + delta) true p1;
      begin match p2 with
      | PTick (0, _) -> ()
      | _ ->
        printf "\n"; idnt lvl; printf "else\n";
        g (lvl + delta) true p2
      end
    | PWhile (c, p, _) ->
      printf "while "; cond c; printf "\n";
      g (lvl + delta) true p


  and g lvl prns p =
    match p with
    | PSeq (_, _, _) -> f lvl prns p
    | _ ->
      if prns then pre (prog_id p);
      idnt lvl; f lvl prns p;
      if not prns then post (prog_id p)
  in

  let pf {fname; fargs; flocs; fbody} =
    printf "func %s(%a)" fname (pp_list output_string) fargs;
    if flocs <> [] then
      printf " local (%a)\n" (pp_list output_string) flocs
    else
      printf "\n";
    g delta true fbody;
    printf "\n"
  in

  begin
    List.iter pf fl;
    if fl <> [] then printf "\n";
    g 0 false prog;
    printf "\n";
  end

let pp_prog_hooks pre post p = pp_file_hooks pre post ([], p)
let pp_prog p = let f _ = () in pp_file_hooks f f ([], p)
let pp_file = let f _ = () in pp_file_hooks f f


(* tests *)

let test_lexer () =
  let tok = mk_lexer stdin in
  let rec f () =
    let t = tok () in
    Printf.printf "%s\n" (string_of_token t);
    if t <> TEof then f ()
  in f ()

let _ =
  let handle f =
    try f () with
    SyntaxError e -> Printf.eprintf "Syntax error: %s\n" e
  in match try Some Sys.argv.(1) with _ -> None with
  | Some "-tlex" -> handle test_lexer
  | Some "-tparse" -> handle (fun () -> pp_prog (pa_prog stdin))
  | _ -> ()
