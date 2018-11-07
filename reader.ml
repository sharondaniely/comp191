
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(n1), Number(n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;
  
module Reader: sig (*TODO add sig for parsers and then remove*)
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
  val bool_parser : char list -> sexpr * char list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let read_sexpr string = raise X_not_yet_implemented ;;

let read_sexprs string = raise X_not_yet_implemented;;

let bool_parser s = 
  let false_parser = PC.word_ci "#f" in
  let false_packed = PC.pack false_parser (fun (temp)-> Bool(false)) in
  let true_parser = PC.word_ci "#t" in
  let true_packed = PC.pack true_parser (fun (temp)-> Bool(true)) in
  let parsed = PC.disj true_packed false_packed in
  parsed s;;
  
let char_prefix_parser s = 
  let prefix_parser = PC.word "#\\" in
  let prefix_packed = PC.pack prefix_parser (fun (temp) -> Nil) in (*TODO CHECK Nil is good *)
  prefix_packed s;;

let visible_simple_char_parser s = 
  let visible_parser = const (fun (temp)-> (int_of_char temp) > 32) in
  let visiable_packed = PC.pack visible_parser (fun (temp) -> Char(temp)) in
  visiable_packed s;;

let named_char_parser s = 
  let named_parser = const (fun (temp)-> (int_of_char temp) == 0 || (int_of_char temp) == 10 || (int_of_char temp) == 13 || (int_of_char temp) == 9 || (int_of_char temp) == 12 || (int_of_char temp) == 32 ) in
  let named_packed = PC.pack named_parser (fun (temp) -> Char(temp)) in
  named_packed s;;

let hex_char_parser s =
  let hex_parser = 


(*wdklhwljdblwjhwdlhwdlb*)
("sharon comment")
end;; (* struct Reader *)



