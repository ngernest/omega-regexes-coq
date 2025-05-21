open EquivChecker
open Parser

let to_string x = 
        match x with 
        | EQUAL -> "equal"
        | NOT_EQUAL _ -> "not equal"
        | UNKNOWN _ -> "unknown"

let equivalence_checker e1 e2 = 
        Printf.printf "%s" (to_string (check e1 e2))

let main =
  let e1 = OEomega (Echar O) in (* w(0) *)
  let e2 = OEcat (Echar O, OEomega (Echar O)) in (* 0 . w(0) *)
  let e3 = OEomega( Esum (Ecat (Echar O, Echar (S O)), Ecat (Echar (S O), Echar O))) in (* w(01 + 10) *)
  let e4 = OEomega( Esum (Ecat (Echar (S O), Echar O), Ecat (Echar O, Echar (S O)))) in (* w(10 + 01) *)
  let e5 = OEsum  (OEomega(Echar (S O)), OEomega( Echar O)) in (* w(1) + w(0) *)
  let e6 = OEsum (OEomega (Echar O), OEomega( Echar (S O))) in (* w(0) + w(1) *)
  let e7 = OEsum  (OEomega(Echar (S O)), OEomega( Echar (S (S O)))) in  (* w(1) + w(2) *)
  let e8 = get_omega_exp "w(0)" in
  (*Printf.printf "result %b %`\n" (check e1 e2) (check e5 e6)*)
  Printf.printf "%s and %s and %s and %s and %s" (to_string (check e1 e2)) (to_string (check e3 e4)) (to_string (check e5 e6)) (to_string (check e7 e6)) (to_string (check e1 e8))

