(* Parsing and definition of programs *)
exception SyntaxError of string

(* lexing *)

type token =
  | TAssert | TWhile | TIf | TElse | TBreak
  | TSemi | TPlus | TMinus | TStar
  | TLParen | TRParen
  | TLt | TGt | TLe | TGe | TEq
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
      else TIdnt s
    | ('0' .. '9') as c -> TNum (getnum (digit c))
    | ';' -> TSemi | '+' -> TPlus | '-' -> TMinus | '*' -> TStar
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
  | TSemi -> "SEMI" | TStar -> "STAR"
  | TPlus -> "PLUS" | TMinus -> "MINUS"
  | TLParen -> "LPAREN" | TRParen -> "RPAREN"
  | TLt -> "LT" | TGt -> "GT"
  | TLe -> "LE" | TGe -> "GE"
  | TEq -> "EQ"
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
type cond = C of lsum * comp * lsum

type prog =
  | PSkip of uid
  | PBreak of uid
  | PAssert of cond * uid
  | PInc of id * op * var * uid
  | PSet of id * var * uid
  | PWhile of cond * prog * uid
  | PIf of cond * prog * prog * uid
  | PSeq of prog * prog * uid

(* parser for one program *)
let p_prog: prog pm =

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
    ; bnd (p_tok (is TLParen)) (fun () ->
      bnd (p_lsum ()) (fun l ->
      bnd (p_tok (is TRParen)) (fun () ->
        ret l
      )))

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

  let p_cond () =
    let comp = function
      | TLe -> Some CLe
      | TGe -> Some CGe
      | TLt -> Some CLt
      | TGt -> Some CGt
      | _ -> None in
    bnd (p_lsum ()) (fun left ->
    bnd (p_tok comp) (fun c ->
    bnd (p_lsum ()) (fun right ->
      ret (C (left, c, right))
    ))) in

  let rec p_atomic () = p_or

    (* Increment/Decrement, PInc *)
    [ bnd (p_tok idnt) (fun id ->
      bnd (p_tok (is TEq)) (fun () ->
      bnd (p_tok (is (TIdnt id))) (fun () ->
      bnd (p_tok binop) (fun op ->
      bnd p_var (fun v ->
        reti (fun i -> PInc (id, op, v, i))
      )))))

    (* Assignment, PSet *)
    ; bnd (p_tok idnt) (fun id ->
      bnd (p_tok (is TEq)) (fun () ->
      bnd p_var (fun v ->
        reti (fun i -> PSet (id, v, i))
      )))

    (* Skip, PSkip *)
    ; bnd (p_tok (is TLParen)) (fun () ->
      bnd (p_tok (is TRParen)) (fun () ->
        reti (fun i -> PSkip i)
      ))

    (* Break, PBreak *)
    ; bnd (p_tok (is TBreak)) (fun () ->
	reti (fun i -> PBreak i)
      )

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
        (* No else part, implicit skip *)
        ; bnd (reti (fun i -> PSkip i)) (fun p2 ->
            reti (fun i -> PIf (cond, p1, p2, i))
          )
        ]
      )))

    (* Parenthesized complex statement *)
    ; bnd (p_tok (is TLParen)) (fun () ->
      bnd (p_complex ()) (fun prog ->
      bnd (p_tok (is TRParen)) (fun () ->
        ret prog
      )))
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

  bnd (p_complex ()) (fun prog ->
  p_or
    [ bnd (p_tok (fun x -> Some (string_of_token x)))
      (fun t -> raise (SyntaxError ("unexpected token " ^ t)))
    ; ret prog
    ]
  )

let pa_prog ic =
  match p_prog (1, stream_of_fun (mk_lexer ic)) with
  | (Some p, _) -> p
  | (None, _) -> raise (SyntaxError "parse error")

let prog_id = function
  | PSkip id | PBreak id | PAssert (_, id) | PInc (_, _, _, id)
  | PSet (_, _, id) | PWhile (_, _, id) | PIf (_, _, _, id)
  | PSeq (_, _, id) -> id


(* pretty printing *)

let pp_var oc = function
  | VNum n -> Printf.fprintf oc "%d" n
  | VId x -> Printf.fprintf oc "%s" x


let pp_prog_hooks pre post prog =
  let open Printf in

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
    | C (l1, cmp, l2) ->
      lsum false l1;
      printf " %s " (
        match cmp with
        | CLe -> "<="
        | CGe -> ">="
        | CLt -> "<"
        | CGt -> ">"
      );
      lsum false l2 in

  let rec idnt i =
    if i <> 0 then
      begin print_string " "; idnt (i - 1) end in

  let delta = 2 in

  let rec f lvl prns = function
    | PSkip _ -> printf "()"
    | PBreak _ -> printf "break"
    | PAssert (c, _) -> printf "assert "; cond c
    | PSet (id, v, _) -> printf "%s = %a" id pp_var v
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
      | PSkip _ -> ()
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

  in g 0 false prog; printf "\n"

let pp_prog = let f _ = () in pp_prog_hooks f f


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
