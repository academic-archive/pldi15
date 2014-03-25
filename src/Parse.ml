(* Parsing and definition of programs *)
exception SyntaxError of string

(* lexing *)

type token =
  | TWhile
  | TSemi | TPlus | TMinus
  | TLParen | TRParen
  | TLt | TGt | TEq
  | TIdnt of string
  | TNum of int
  | TEof

let mk_lexer ic =

  let (next, back) =
    let mem = ref None in
    (fun () ->
      match !mem with
      | None -> (try input_char ic with _ -> '\xff')
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
      else TIdnt s
    | ('0' .. '9') as c -> TNum (getnum (digit c))
    | ';' -> TSemi | '+' -> TPlus | '-' -> TMinus
    | '(' -> TLParen | ')' -> TRParen
    | '<' -> TLt | '>' -> TGt | '=' -> TEq
    | '\xff' -> TEof
    | ' ' | '\t' | '\r' | '\n' -> f ()
    | _ -> raise (SyntaxError "lexing")

  in f

let string_of_token = function
  | TWhile -> "WHILE"
  | TIdnt id -> Printf.sprintf "IDNT %S" id
  | TNum n -> Printf.sprintf "NUM %d" n
  | TSemi -> "SEMI"
  | TPlus -> "PLUS" | TMinus -> "MINUS"
  | TLParen -> "LPAREN" | TRParen -> "RPAREN"
  | TLt -> "LT" | TGt -> "GT" | TEq -> "EQ"
  | TEof -> "EOF"


(* parsing *)

type stream_strict = SEof | STok of token * stream
and stream = stream_strict lazy_t

let rec stream_of_fun f = lazy (
  match f () with
  | TEof -> SEof
  | tok -> STok (tok, stream_of_fun f)
)


type 'a pm = stream -> 'a option * stream
let ret x = fun s -> (Some x, s)
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

let p_tok f s =
  match Lazy.force s with
  | STok (tok, s') ->
    begin match f tok with
    | None -> (None, s)
    | Some x -> (Some x, s')
    end
  | _ -> (None, s)


type var = string
type op = OPlus | OMinus
(* Conditions are of the form v1 - v2 < k *)
type cond = Cond of var * var * int

type prog =
  | PSkip
  | PSeq of prog * prog
  | PInc of var * op * var
  | PSet of var * var
  | PWhile of cond * prog

(* parser for one program *)
let p_prog: prog pm =

  let is t t' = if t = t' then Some () else None in
  let const = function TNum n -> Some n | _ -> None in
  let idnt = function TIdnt id -> Some id | _ -> None in
  let binop = function
    | TPlus -> Some OPlus
    | TMinus -> Some OMinus
    | _ -> None in
  let var = function
    | TIdnt id -> Some id
    | TNum n -> Some ("$" ^ string_of_int n)
    | _ -> None in

  let p_cond = p_or

    (* x > k *)
    [ bnd (p_tok idnt) (fun id ->
      bnd (p_tok (is TGt)) (fun () ->
      bnd (p_tok const) (fun k ->
        ret (Cond (id, "$0", k))
      )))

    (* x - y > k *)
    ; bnd (p_tok var) (fun v1 ->
      bnd (p_tok (is TMinus)) (fun () ->
      bnd (p_tok var) (fun v2 ->
      bnd (p_tok (is TGt)) (fun () ->
      bnd (p_tok const) (fun k ->
        ret (Cond (v1, v2, k))
      )))))

    (* anything else is invalid *)
    ; fun _ -> raise (SyntaxError "unsupported condition")
    ] in

  let rec p_atomic () = p_or

    (* Increment/Decrement, PInc *)
    [ bnd (p_tok idnt) (fun id ->
      bnd (p_tok (is TEq)) (fun () ->
      bnd (p_tok (is (TIdnt id))) (fun () ->
      bnd (p_tok binop) (fun op ->
      bnd (p_tok var) (fun v ->
        ret (PInc (id, op, v))
      )))))

    (* Assignment, PSet *)
    ; bnd (p_tok idnt) (fun id ->
      bnd (p_tok (is TEq)) (fun () ->
      bnd (p_tok var) (fun v ->
        ret (PSet (id, v))
      )))

    (* Skip, PSkip *)
    ; bnd (p_tok (is TLParen)) (fun () ->
      bnd (p_tok (is TRParen)) (fun () ->
        ret PSkip
      ))

    (* While loop, PWhile *)
    ; bnd (p_tok (is TWhile)) (fun () ->
      bnd p_cond (fun cond ->
      bnd (p_atomic ()) (fun prog ->
        ret (PWhile (cond, prog))
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
            ret (PSeq (prog1, prog2))
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

let prog s =
  match p_prog s with
  | (Some p, _) -> p
  | (None, _) -> raise (SyntaxError "parse error")

let pp_prog =
  let string_of_var s =
    if s.[0] <> '$' then s else
    String.sub s 1 (String.length s - 1) in
  let open Format in
  let rec f prns fmt = function
    | PSkip -> fprintf fmt "()"
    | PSeq (p1,  p2) ->
      (if prns
        then fprintf fmt "(@[<v 2>@;%a;@;%a@]@;)"
        else fprintf fmt "%a;@;%a")
      (f true) p1 (f false) p2
    | PInc (id, o, v) ->
      let op = match o with OPlus -> "+" | OMinus -> "-" in
      fprintf fmt "%s = %s %s %s" id id op (string_of_var v)
    | PSet (id, v) ->
      fprintf fmt "%s = %s" id (string_of_var v)
    | PWhile (Cond (v1, v2, k), p) ->
      fprintf fmt "while %s - %s > %d@.  @[<v>%a@]"
        (string_of_var v1) (string_of_var v2) k
        (f true) p
  in Format.printf "@[<v>%a@]@." (f false)


(* tests *)

let test_lexer () =
  try
    let tok = mk_lexer stdin in
    let rec f () =
      let t = tok () in
      Printf.printf "%s\n" (string_of_token t);
      if t <> TEof then f ()
    in f ()
  with SyntaxError e -> Printf.eprintf "Syntax error: %s\n" e

let test_parser () =
  try
    let lexer = mk_lexer stdin in
    let p = prog (stream_of_fun lexer) in
    pp_prog p
  with SyntaxError e -> Printf.eprintf "Syntax error: %s\n" e

let _ =
  match try Some Sys.argv.(1) with _ -> None with
  | Some "-tlex" -> test_lexer ()
  | Some "-tparse" -> test_parser ()
  | _ -> ()
