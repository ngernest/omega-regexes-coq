open Deriv

type token = SYM of int | EPS | LP | RP | SUM | CAT | STAR | OMEGA 
type exp = Sym of int | Epsilon | Sum of exp * exp | Cat of exp * exp | Star of exp | Omega of exp 
exception Error of string

let isDigit d = match d with
  |'0'..'9' -> true
  | _ -> false
let num c = Char.code c - Char.code '0'
let explode s = List.init (String.length s) (String.get s)

let rec lex s = match s with 
  | [] -> []
  | ' '::s' | '\n'::s' | '\t'::s' -> lex s' 
  | '('::s' -> LP::lex s'
  | ')'::s' -> RP::lex s'
  | '+'::s' -> SUM::lex s'
  | '.'::s' -> CAT::lex s' 
  | '*'::s' -> STAR::lex s' 
  | 'e'::s' -> EPS::lex s'
  | 'w'::s' -> OMEGA::lex s' 
  | c::s' -> if isDigit c then lexNum (c::s') else raise (Error "lex")
and lexNum cl =
  let rec numAcc v cl =
    if cl = [] || not(isDigit (List.hd cl))
    then SYM v :: (lex cl)
    else numAcc (10 * v + num (List.hd cl)) (List.tl cl)
  in numAcc 0 cl 

let rec cexp tl = match aexp tl with 
  | (e, SUM::l) -> let (e',tl') = cexp l in (Sum(e,e'),tl')
  | t -> t
and aexp tl = match sexp tl with 
  | (e, CAT::l) -> let (e',tl') = aexp l in (Cat(e,e'),tl')
  | t -> t
and sexp tl = match tl with 
  | STAR::LP::tl' -> (match cexp tl' with 
      | (e,RP::tl') -> (Star e,tl')
      | _ -> raise (Error "star" ))
  | OMEGA::LP::tl' -> (match cexp tl' with 
      | (e, RP::tl') -> (Omega e, tl')
      | _ -> raise (Error "omega" ))
  | _ -> pexp tl 
and pexp tl = match tl with 
  | SYM x::tl' -> (Sym x, tl')
  | EPS::tl' -> (Epsilon, tl')
  | LP::l -> (match cexp l with 
      | (e, RP::tl') -> (e, tl')
      | _ -> raise (Error "parantheses"))
  | _ -> raise (Error "parse")

let rec parse tl = let (e,t) = cexp tl in 
  if t = [] then e else raise (Error "parse")
        
let rec parse_reg e = match e with 
        | Sym x -> Echar x 
        | Epsilon -> One 
        | Sum(a,b) -> Esum(parse_reg a, parse_reg b)
        | Cat(a,b) -> Ecat(parse_reg a, parse_reg b)
        | Star(a) -> Estar(parse_reg a)
        | _ -> raise (Error "parse regular")

let rec parse_omega e = match e with 
        | Sum(a,b) -> OEsum (parse_omega a, parse_omega b)
        | Cat(a,b) -> OEcat (parse_reg a, parse_omega b)
        | Omega(a) -> OEomega (parse_reg a) 
        | _ -> raise (Error "parse omega")

let get_omega_exp s = parse_omega (parse (lex (explode s)))
