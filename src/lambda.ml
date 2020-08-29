(* Simple lambda calcul *)
type term =
  | Var of string
  | Lamb of string * term
  | App of term * term

(* Replace free occurences of symbol x by the term y in a term *)
let rec subst x y = function
  | Var x' when x = x' -> y
  | Lamb (x', t) when x <> x' -> Lamb (x', subst x y t)
  | App (t1, t2) -> App (subst x y t1, subst x y t2)
  | _ as t -> t

(* Alpha conversion *)
let rec alpha x y = subst x (Var y)

(* Alpha normalization *)
let alpha_norm t =
  let count = ref 0 in
  let rec step = function
    | Lamb (x, t) ->
      incr count;
      let x' = Printf.sprintf "x_%d" !count in
      Lamb (x', (step (alpha x x' t)))
    | App (t1, t2) -> App (step t1, step t2)
    | _ as t -> t
  in
  step t

(* Beta Reduction *)
let rec beta = function
  | Var _ as t -> t
  | App (x, y) ->
    begin match beta x with
      | Lamb (x', t) -> beta (subst x' (beta y) t)
      | _ as t -> App (t, beta y)
    end
  | Lamb (x, t) -> Lamb (x, beta t)

let rec beta_safe n t =
  if n <= 0 then failwith "too many reduction steps !"
  else begin match t with
    | Var _ -> t
    | App (x, y) ->
      begin match beta_safe (n - 1) x with
        | Lamb (x', t) -> beta_safe (n - 1) (subst x' (beta_safe (n - 1) y) t)
        | _ as t -> App (t, beta_safe (n - 1) y)
      end
    | Lamb (x, t) -> Lamb (x, beta_safe (n - 1) t)
  end

(* Simple evaluation *)
let eval t = t |> alpha_norm |> beta