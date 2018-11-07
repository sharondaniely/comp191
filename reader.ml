
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
  val digit_parser : char list -> char * char list
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
  let visible_parser = PC.const (fun (temp)-> (int_of_char temp) > 32) in
  let visiable_packed = PC.pack visible_parser (fun (temp) -> Char(temp)) in
  visiable_packed s;;

let named_char_parser s = 
  let named_parser = PC.const (fun (temp)-> (int_of_char temp) == 0 
                                          || (int_of_char temp) == 10 
                                          || (int_of_char temp) == 13 
                                          || (int_of_char temp) == 9 
                                          || (int_of_char temp) == 12 
                                          || (int_of_char temp) == 32 ) in
  let named_packed = PC.pack named_parser (fun (temp) -> Char(temp)) in
  named_packed s;;















(*******************************numbers**********************************)


let digit_parser =  PC.range '0' '9'
;;

let natural_parser s   =
let natural_helper = PC.plus digit_parser in
let packed_natural_parser = PC.pack natural_helper (fun (temp)-> int_of_string (list_to_string temp)) in
packed_natural_parser s;;

let sign_parser s =
  let sign_helper = PC.const (fun (temp)-> temp = '-' || temp = '+') in
    let parser = PC.pack sign_helper (fun (temp)-> temp) in
    parser s;;

let signed_integer_parser s =
  let integer_helper = PC.pack (PC.caten sign_parser natural_parser ) (fun (temp)-> if ((fst temp) = '-') 
                                                                                        then Number(Int ((-1)*(snd temp)))
                                                                                        else Number(Int (snd temp))) in
  integer_helper s;;

 let not_signed_integer_parser s =
    PC.pack natural_parser (fun (temp)-> Number(Int(temp))) s;;

let integer_parser s = (PC.disj signed_integer_parser not_signed_integer_parser) s;;


(** *************************************HEX***************************************)

let hex_prefix s = PC.pack (PC.word_ci "#x") (fun (temp)-> Nil) s;;

let hex_natural_parser s = PC.pack (PC.plus hex_digit_parser) s;;

let not_signed_hex_integer_parser s =
  PC.pack (PC.caten hex_prefix hex_natural_parser) (fun (temp)-> Number(Int (int_of_string ( "0x" ^ (list_to_string(snd temp)))))) s;;
     







end;; (* struct Reader *)



