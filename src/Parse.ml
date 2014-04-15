(* Parsing and definition of programs *)
exception SyntaxError of string

(* lexing *)

type token =
  | TAssert | TWhile
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
  | TAssert -> "ASSERT" | TWhile -> "WHILE"
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
(* Conditions are of the form v1 - v2 > k *)
type cond = Cond of var * var * int

type prog =
  | PSkip of uid
  | PAssert of cond * uid
  | PInc of id * op * var * uid
  | PSet of id * var * uid
  | PWhile of cond * prog * uid
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

  let p_cond = p_or

    (* x > k *)
    [ bnd p_var (fun v ->
      bnd (p_tok (is TGt)) (fun () ->
      bnd p_num (fun k ->
        ret (Cond (v, VNum 0, k))
      )))

    (* x - y > k *)
    ; bnd p_var (fun v1 ->
      bnd (p_tok (is TMinus)) (fun () ->
      bnd p_var (fun v2 ->
      bnd (p_tok (is TGt)) (fun () ->
      bnd p_num (fun k ->
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

    (* While loop, PWhile *)
    ; bnd (p_tok (is TWhile)) (fun () ->
      bnd p_cond (fun cond ->
      bnd (p_atomic ()) (fun prog ->
        reti (fun i -> PWhile (cond, prog, i))
      )))

    (* Assertion, PAssert *)
    ; bnd (p_tok (is TAssert)) (fun () ->
      bnd p_cond (fun cond ->
        reti (fun i -> PAssert (cond, i))
      ))

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
  | PSkip id | PAssert (_, id) | PInc (_, _, _, id) | PSet (_, _, id)
  | PWhile (_, _, id) | PSeq (_, _, id) -> id


(* pretty printing *)

let pp_var oc = function
  | VNum n -> Printf.fprintf oc "%d" n
  | VId x -> Printf.fprintf oc "%s" x


let pp_prog_hooks pre post prog =
  let open Printf in

  let cond = function
    | Cond (v1, VNum 0, k) -> printf "%a > %d" pp_var v1 k
    | Cond (v1, v2, k) -> printf "%a - %a > %d" pp_var v1 pp_var v2 k in

  let rec idnt i =
    if i <> 0 then
      begin print_string " "; idnt (i - 1) end in

  let delta = 2 in

  let rec f lvl prns = function
    | PSkip id -> printf "()"
    | PAssert (c, id) -> printf "assert "; cond c
    | PSet (id, v, _) -> printf "%s = %a" id pp_var v
    | PInc (id, o, v, _) ->
      let op = match o with OPlus -> "+" | OMinus -> "-" in
      printf "%s = %s %s %a" id id op pp_var v
    | PSeq (p1,  p2, _) ->
      let lvl' = if prns then (idnt lvl; printf "(\n"; lvl + delta) else lvl in
      g lvl' true p1; printf ";\n";
      g lvl' false p2;
      if prns then (printf "\n"; idnt lvl; printf ")")
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
