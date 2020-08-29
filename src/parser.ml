open Lambda

(* type for parsers *)
type 'a parser = string -> ('a * string) option

(* "Zero" parser *)
let p_zero _ = None

(* Return *)
let p_return x = fun s -> Some (x, s)

(* "Any" parser *)
let p_any = function
  | "" -> None
  | _ as s -> Some (s.[0], String.(sub s 1 (length s - 1)))

(* Bind *)
let (>>=) (p : 'a parser) f = fun s ->
  match p s with
  | None -> None
  | Some (x, rem) -> (f x) rem

(* Check *)
let p_check pred = p_any >>= (fun res -> if pred res then p_return res else p_zero)

(* Map *)
let (=>) p f = p >>= fun r -> p_return (f r)

(* Ignore left *)
let (>>) p q = p >>= fun _ -> q

(* Ignore right *)
let (<<) p q = p >>= fun r -> q >>= fun _ -> p_return r

(* Chain *)
let (<~>) p ps = p >>= fun r -> ps >>= fun rs -> p_return (r::rs)

(* Choice *)
let (<|>) (p : 'a parser) (q : 'a parser) = fun s ->
  match p s with
  | Some x -> Some x
  | None -> q s

let p_char c : char parser = p_check ((=) c)

let rec p_some (p : 'a parser) : 'a list parser = fun s ->
  match p s with
  | None -> Some ([], s)
  | Some (x, rem) ->
    match p_some p rem with
    | None -> Some ([x], rem)
    | Some (xs, rem) -> Some (x::xs, rem)

let p_many (p : 'a parser) = p >>= (fun c -> p_some p => List.cons c)

let p_between a b p = a >> p << b

let p_parens a b = p_between (p_char a) (p_char b)

let p_blank = p_char ' ' <|> p_char '\n' <|> p_char '\t'

let p_blanks = p_some p_blank

let p_token p = p_blanks >> p

let rec combine_app = function
  | [] -> assert false
  | [x] -> x
  | x::y::xs -> combine_app (App (x, y)::xs)

let rec term inp =
  let id = p_check (function 'a'..'z' -> true | _ -> false) => String.make 1 in
  let var = id => fun v -> Var v in
  let pterm = p_parens '(' ')' term in
  let lam = p_char '\\' >> 
    id >>= fun v ->
    p_char '.' >>
    term >>= fun t -> p_return (Lamb (v, t)) in
  let app = p_many ((pterm <|> var <|> lam) << p_blanks) => combine_app in
  (app <|> var <|> lam <|> pterm) inp

let _ = match (term => alpha_norm) "(\\x.x x) (\\x.x x)" with
  | None -> failwith "err"
  | Some (x, _) -> beta_safe 10 x