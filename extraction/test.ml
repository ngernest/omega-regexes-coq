open Deriv
open Parser

let to_string x = 
        match x with 
        | EQUAL -> "equal"
        | NOT_EQUAL _ -> "not equal"
        | DONT_KNOW _ -> "don't know"

let equivalence_checker e1 e2 = 
        Printf.printf "%s" (to_string (check e1 e2))

let main =
  let e1 = OEomega (Echar O) in
  let e2 = OEcat (Echar O, OEomega (Echar O)) in
  let e3 = OEomega( Esum (Ecat (Echar O, Echar (S O)), Ecat (Echar (S O), Echar O))) in 
  let e4 = OEomega( Esum (Ecat (Echar (S O), Echar O), Ecat (Echar O, Echar (S O)))) in 
  let e5 = OEsum  (OEomega(Echar (S O)), OEomega( Echar O)) in 
  let e6 = OEsum (OEomega (Echar O), OEomega( Echar (S O))) in 
  let e7 = OEsum  (OEomega(Echar (S O)), OEomega( Echar (S (S O)))) in 
  let e8 = OEsum (OEomega (Echar O), OEomega( Echar (S O))) in 
  (*Printf.printf "result %b %`\n" (check e1 e2) (check e5 e6)*)
  Printf.printf "%s and %s and %s and %s" (to_string (check e1 e2)) (to_string (check e3 e4)) (to_string (check e5 e6)) (to_string (check e7 e8))



