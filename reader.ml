
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;
open PC 

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
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;
  
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

(*let read_sexpr string = raise X_not_yet_implemented;;*)
(*let read_sexprs string = raise X_not_yet_implemented;;*)



let symbol_char_digits_parser s =
  let number_range_parser = PC.range '0' '9' in
  let number_range_packed = PC.pack number_range_parser (fun (temp)-> temp) in
  let lower_case_range_parser = PC.range 'a' 'z' in
  let lower_case_range_packed = PC.pack lower_case_range_parser (fun (temp)-> temp) in
  let upper_case_range_parser = PC.range 'A' 'Z' in
  let upper_case_range_packed = PC.pack upper_case_range_parser (fun (temp)-> (lowercase_ascii temp)) in
  let digits_packed = PC.disj number_range_packed (PC.disj lower_case_range_packed upper_case_range_packed) in
  digits_packed s;;


let symbol_char_parser s =
  let signs_praser = PC.disj_list [PC.char '!'; PC.char '$'; PC.char '^'; PC.char '*'; PC.char '-'; PC.char '_'; PC.char '='; PC.char '+';
  PC.char '<'; PC.char '>'; PC.char '?'; PC.char '/'; PC.char ':'] in
  let signs_packed = PC.pack signs_praser (fun(temp) -> temp) in
  let symbol_char_packed = PC.disj symbol_char_digits_parser signs_packed in
  symbol_char_packed s;;

let bool_parser s = 
  let false_parser = PC.word_ci "#f" in
  let false_packed = PC.pack false_parser (fun (temp)-> Bool(false)) in
  let true_parser = PC.word_ci "#t" in
  let true_packed = PC.pack true_parser (fun (temp)-> Bool(true)) in
  let illegal_extention_parser = symbol_char_parser in
  let parsed = PC.disj true_packed false_packed in
  let packed = PC.not_followed_by parsed illegal_extention_parser in
  packed s;;
  
(** ************************************CHAR*****************************************)

let char_prefix_parser s = 
  let prefix_parser = PC.word "#\\" in
  let prefix_packed = PC.pack prefix_parser (fun (temp) -> Nil) in
  prefix_packed s;;

let visible_simple_char_parser s = 
  let visible_parser = PC.const (fun (temp)-> (int_of_char temp) > 32) in
  let visiable_packed = PC.pack visible_parser (fun (temp) -> Char(temp)) in
  visiable_packed s;;

let hex_digit_parser_numbers  = PC.disj_list [PC.range '0' '9'; PC.range 'a' 'f'; PC.range 'A' 'F'];;



let hex_digit_parser s =
  let number_range_parser = PC.range '0' '9' in
  let number_range_packed = PC.pack number_range_parser (fun (temp)-> temp) in
  let lower_case_range_parser = PC.range 'a' 'f' in
  let lower_case_range_packed = PC.pack lower_case_range_parser (fun (temp)-> temp) in
  let upper_case_range_parser = PC.range 'A' 'F' in
  let upper_case_range_packed = PC.pack upper_case_range_parser (fun (temp)-> temp) in
  let hex_packed = PC.disj number_range_packed (PC.disj lower_case_range_packed upper_case_range_packed) in
  hex_packed s;;






let named_char_parser s =
  let named_packed = PC.disj_list [
  PC.pack (PC.word_ci "nul") (fun (temp) -> Char(char_of_int 0))
  ; PC.pack (PC.word_ci "newline") (fun (temp) -> Char(char_of_int 10))
  ; PC.pack (PC.word_ci "return") (fun (temp) -> Char(char_of_int 13))
  ; PC.pack (PC.word_ci "tab") (fun (temp) -> Char(char_of_int 9))
  ; PC.pack (PC.word_ci "page") (fun (temp) -> Char(char_of_int 12))
  ; PC.pack (PC.word_ci "space") (fun (temp) -> Char(char_of_int 32))] in
  named_packed s;;



let hex_char_parser s =
  let x_parser = PC.char_ci 'x' in
  let hex_parser = PC.caten x_parser (PC.plus hex_digit_parser) in
  let hex_packed = PC.pack hex_parser (fun (temp)->  Char (char_of_int (int_of_string ( "0x" ^ (list_to_string (snd temp) ))))) in
  hex_packed s;;

let char_parser s =
  let parser = PC.caten char_prefix_parser (PC.disj hex_char_parser (PC.disj named_char_parser visible_simple_char_parser) ) in
  let packed = PC.pack parser (fun (temp)-> (snd temp)) in
  let illegal_extention_parser = symbol_char_parser in
  let char_parser_packed = PC.not_followed_by packed illegal_extention_parser in
  char_parser_packed s;;








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
                                                                                        then (-1)*(snd temp)
                                                                                        else snd temp) in
  integer_helper s;;

 let not_signed_integer_parser s =
    PC.pack natural_parser (fun (temp)-> temp) s;;

let integer_parser s = PC.pack 
                      (PC.disj signed_integer_parser not_signed_integer_parser)
                      (fun (temp)-> Number(Int(temp))) s;;


(** *************************************HEX***************************************)

let hex_prefix s = PC.pack (PC.word_ci "#x") (fun (temp)-> Nil) s;;

let hex_natural_parser s = PC.pack (PC.plus hex_digit_parser) (fun (temp)-> temp) s;;

let not_signed_hex_integer_parser s =
  PC.pack (PC.caten hex_prefix hex_natural_parser) (fun (temp)-> int_of_string ( "0x" ^ (list_to_string(snd temp)))) s;;
     
let signed_hex_integer_parser s =
  PC.pack (PC.caten hex_prefix ( PC.caten sign_parser hex_natural_parser)) (fun (temp)-> if ( (fst(snd temp)) = '+')
                                                                                                then int_of_string ( "0x" ^ (list_to_string(snd (snd temp))))
                                                                                                else (-1)* (int_of_string ( "0x" ^ (list_to_string(snd (snd temp))))))
                                                                                                s;;

let hex_integer_parser s = PC.pack
                                (PC.disj signed_hex_integer_parser not_signed_hex_integer_parser) 
                                (fun (temp)-> Number(Int (temp)))
                                s;;


(***************************INTEGER FLOAT******************************* *)

let dot_parser s = PC.pack (PC.char '.') (fun (temp)-> temp) s;;

let not_siged_flaot_parser s = 
    PC.pack (PC.caten not_signed_integer_parser (PC.caten dot_parser natural_parser))
    (fun (temp)-> float_of_string( (string_of_int (fst temp))^ "." ^ string_of_int(snd(snd(temp)))))
    s;;

let siged_flaot_parser s = 
    PC.pack (caten sign_parser (caten natural_parser (caten dot_parser natural_parser)))
    (fun (temp)-> if  ((fst temp) = '-')
                  then (-1.0)*. float_of_string((string_of_int(fst(snd temp)))^ "." ^ (string_of_int(snd(snd(snd(temp))))))
                  else  float_of_string((string_of_int(fst(snd temp)))^ "." ^ (string_of_int(snd(snd(snd(temp))))))) 
    s;;

let float_parser s = PC.pack 
                    (PC.disj siged_flaot_parser not_siged_flaot_parser)
                    (fun (temp)-> Number(Float(temp)))
                     s;; 


(********************************HEX FLOAT **************************************** *)


(********************************HEX FLOAT *****************************************)
(** TODO*)
let not_siged_hex_flaot_parser s = 
    PC.pack (PC.caten not_signed_hex_integer_parser (PC.caten dot_parser hex_natural_parser))
    (fun (temp)-> (float_of_int (fst temp)) +. float_of_string( "0x0." ^ (list_to_string(snd(snd(temp))))))
    s;;

let siged_hex_flaot_parser s =
    PC.pack (PC.caten hex_prefix (caten sign_parser (caten hex_natural_parser (PC.caten dot_parser hex_natural_parser))))
    (fun (temp)-> if ((fst(snd temp)) = '-') 
                  then (-1.0)*.((float_of_string ("0x" ^(list_to_string(fst(snd(snd temp)))))) +. float_of_string( "0x0." ^ (list_to_string(snd(snd(snd(snd temp)))))))
                  else (float_of_string ("0x" ^(list_to_string(fst(snd(snd temp)))))) +. float_of_string( "0x0." ^ (list_to_string(snd(snd(snd(snd temp)))))))
    s;;

let hex_float_parser s = PC.pack 
                    (PC.disj siged_hex_flaot_parser not_siged_hex_flaot_parser)
                    (fun (temp)-> Number(Float(temp)))
                     s;; 



(*
let scientific_float_parser_helper string =
  pack (caten (disj siged_flaot_parser not_siged_flaot_parser)
        (caten (word_ci "e") (disj signed_integer_parser not_signed_integer_parser))) 
  (fun (temp) -> ((fst temp)*.(10.0**(float_of_int(snd(snd temp))))))
  string;;


let scientific_float_parser string =
  pack scientific_float_parser_helper
  (fun (temp) -> if (temp = float_of_int(int_of_float(temp)))
  then Number(Int(int_of_float(temp)))
  else Number(Float(temp)))
  string;;

let scientific_int_parser_helper string =
  pack (caten (disj signed_integer_parser not_signed_integer_parser)
        (caten (word_ci "e") (disj signed_integer_parser not_signed_integer_parser))) 
  (fun (temp) -> (float_of_int(fst temp))*.(10.0**(float_of_int(snd(snd temp))))) 
  string;;


let scientific_int_parser string =
  pack scientific_int_parser_helper
  (fun (temp) -> if (temp = float_of_int(int_of_float(temp)))
  then Number(Int(int_of_float(temp)))
  else Number(Float(temp)))
  string;;
*)


let scientific_float_parser_helper string =
  pack (caten (disj siged_flaot_parser not_siged_flaot_parser)
        (caten (word_ci "e") (disj signed_integer_parser not_signed_integer_parser))) 
  (fun (temp) -> ((fst temp)*.(10.0**(float_of_int(snd(snd temp))))))
  string;;


let scientific_float_parser string =
  pack scientific_float_parser_helper
  (fun (temp) -> if (temp = float_of_int(int_of_float(temp)))
  then Number(Float(temp))
  else Number(Float(temp)))
  string;;

let scientific_int_parser_helper string =
  pack (caten (disj signed_integer_parser not_signed_integer_parser)
        (caten (word_ci "e") (disj signed_integer_parser not_signed_integer_parser))) 
  (fun (temp) -> (float_of_int(fst temp))*.(10.0**(float_of_int(snd(snd temp))))) 
  string;;


let scientific_int_parser string =
  pack scientific_int_parser_helper
  (fun (temp) -> if (temp = float_of_int(int_of_float(temp)))
  then Number(Float(temp))
  else Number(Float(temp)))
  string;;



let number_parser string  = 
  let illegal_extention_parser = symbol_char_parser in
  PC.not_followed_by (PC.disj_list [ hex_float_parser ; scientific_float_parser; float_parser ; hex_integer_parser ; scientific_int_parser; integer_parser]) illegal_extention_parser 
  string;;








let symbol_parser s =
  let symbol_parser = PC.plus symbol_char_parser in
  let symbol_packed = PC.pack symbol_parser (fun (temp) -> Symbol(list_to_string temp)) in
  symbol_packed s;; 


(**************************************string******************************* *)




let string_literal_char_parser s =
  let literal_char_parser = PC.const (fun (temp) -> (int_of_char temp) != 92 && (int_of_char temp) != 34) in
  let literal_char_packed = PC.pack literal_char_parser (fun (temp) -> temp) in
  literal_char_packed s;;

let string_meta_char_parser s =
  let meta_char_parser = PC.disj_list [
    PC.pack (PC.word "\\r") (fun (temp) -> char_of_int(13))
    ; PC.pack (PC.word "\\n") (fun (temp) -> char_of_int(10))
    ; PC.pack (PC.word "\\t") (fun (temp) -> char_of_int(9))
    ; PC.pack (PC.word "\\f") (fun (temp) -> char_of_int(12))
    ; PC.pack (PC.word "\\\\") (fun (temp) -> char_of_int(92))
    ; PC.pack (PC.word "\\\"") (fun (temp) -> char_of_int(34))
  ] in
  meta_char_parser s;;



let string_hex_char_parser s =
  let prefix_parser = PC.word_ci "\\x" in
  let closing_parser = PC.word ";" in
  let hex_char_parser = PC.plus hex_digit_parser in
  let hex_char_packed = PC.pack (PC.caten prefix_parser (PC.caten hex_char_parser closing_parser)) (fun (temp) -> char_of_int(int_of_string ("0x" ^ (list_to_string(fst(snd temp)))))) in
  hex_char_packed s;;

let string_char_parser s =
  let string_char_packed = PC.disj_list [string_hex_char_parser; string_literal_char_parser; string_meta_char_parser] in
  string_char_packed s;;

let string_parser s =
    let first_quote_parser = PC.char (char_of_int 34) in
    let body_of_string_parser = PC.pack (PC.star string_char_parser) (fun(temp) -> list_to_string(temp)) in
    let second_quote_parser = PC.char (char_of_int 34) in
    let string_packed = PC.pack (PC.caten first_quote_parser (PC.caten body_of_string_parser second_quote_parser)) (fun (temp) -> String(fst(snd(temp)))) in
    let illegal_extention_parser = symbol_char_parser in
    let string_parser_packed = PC.not_followed_by string_packed illegal_extention_parser in
    string_parser_packed s;;




let white_spaces_parser s =
  let spaces_parser = PC.const (fun (temp) -> (int_of_char temp) < 33) in
  let spaces_packed = PC.pack spaces_parser (fun (temp) -> Nil) in
  spaces_packed s;;


let line_comments_parser s =
  let semicolon_parser = PC.word ";" in
  let body_of_comment_parser = PC.star (PC.const (fun(temp) -> (int_of_char temp) != 10)) in
  let end_of_comment_parser = PC.const (fun (temp) -> (int_of_char temp) = 10) in
  let everything_parser = PC.const (fun (temp) -> (int_of_char temp) > -1 ) in
  let end_of_input_parser = PC.not_followed_by (PC.word "") everything_parser in
  let end_of_input_packed = PC.pack end_of_input_parser (fun (temp) -> 'a') in
  let disj_end_of_comment_parser = PC.disj end_of_comment_parser end_of_input_packed in
  let line_comment_parser = PC.caten semicolon_parser (PC.caten body_of_comment_parser disj_end_of_comment_parser) in
  let line_comments_packed = PC.pack line_comment_parser (fun (temp) -> Nil) in
  line_comments_packed s;;

let rec sexpr_parser string =
      PC.pack (PC.caten disj_stars_comments_white_spaces (PC.caten (PC.disj_list [s_parser;bool_parser;
                             char_parser;
                            number_parser;
                            string_parser;
                            symbol_parser;
                            list_parser;
                            special_list_parser;
                            dotted_list_parser;
                            special_dotted_list_parser;
                            vector_parser;
                            quoted_parser;
                            quasiquote_parser;
                            unquoted_parser;
                            unquoted_spliced_parser;
                            sexpr_comments_parser
                            ]) disj_stars_comments_white_spaces))
       (fun (temp)-> fst(snd(temp)))
        string
    and list_parser s =
          let left_par  = PC.word "(" in
          let right_par = PC.word ")" in
          let sexpr_star = PC.caten disj_stars_comments_white_spaces (PC.caten (PC.star sexpr_parser) disj_stars_comments_white_spaces) in
          PC.pack (PC.caten left_par (PC.caten sexpr_star right_par)) 
          (function (left,((l, (lst, r)),right))-> match lst with
          | []-> Nil
          | _-> (List.fold_right (fun a b -> Pair (a,b)) lst Nil))
          s
    and special_list_parser s =
          let left_par  = PC.word "[" in
          let right_par = PC.word "]" in
          let sexpr_star = PC.caten disj_stars_comments_white_spaces (PC.caten (PC.star sexpr_parser) disj_stars_comments_white_spaces) in
          PC.pack (PC.caten left_par (PC.caten sexpr_star right_par)) 
          (function (left,((l, (lst, r)),right))-> match lst with
          | []-> Nil
          | _-> (List.fold_right (fun a b -> Pair (a,b)) lst Nil))
          s
    and dotted_list_parser s =
          let left_par = PC.word "(" in
          let right_par = PC.word ")" in
          let dot_par = PC.word "." in
          let sexpr_plus = PC.plus sexpr_parser in
          PC.pack (PC.caten left_par (PC.caten sexpr_plus (PC.caten dot_par (PC.caten sexpr_parser right_par))))
          ((function (a,(lst,(b,(sexp,c))))-> match lst with
          | _ -> (List.fold_right (fun a b -> Pair (a,b)) lst sexp))) 
          s
    and special_dotted_list_parser s =
          let left_par = PC.word "[" in
          let right_par = PC.word "]" in
          let dot_par = PC.word "." in
          let sexpr_plus = PC.plus sexpr_parser in
          PC.pack (PC.caten left_par (PC.caten sexpr_plus (PC.caten dot_par (PC.caten sexpr_parser right_par))))
          ((function (a,(lst,(b,(sexp,c))))-> match lst with
          | _ -> (List.fold_right (fun a b -> Pair (a,b)) lst sexp))) 
          s
    and vector_parser s =
          let hash_par = PC.word "#" in
          let left_par = PC.word "(" in
          let right_par = PC.word ")" in
          let sexpr_star = PC.star sexpr_parser in
          PC.pack (PC.caten hash_par (PC.caten left_par (PC.caten sexpr_star right_par)))
          (function (a,(b,(lst,c))) -> match lst with
          | _ -> Vector(lst))
          s
    and quoted_parser s =
         let quote_par = PC.word "'" in
         PC.pack (PC.caten quote_par sexpr_parser)
         (fun (a,b) -> Pair(Symbol("quote"), Pair(b, Nil)))
         s
    and quasiquote_parser s =
         let quasiquote_par = PC.word "`" in
         PC.pack (PC.caten quasiquote_par sexpr_parser)
         (fun (a,b) -> Pair(Symbol("quasiquote"), Pair(b, Nil)))
         s
    and unquoted_parser s =
         let unquoted_par = PC.word "," in
         PC.pack (PC.caten unquoted_par sexpr_parser)
         (fun (a,b) -> Pair(Symbol("unquote"), Pair(b, Nil)))
         s
    and unquoted_spliced_parser s =
         let unquoted_spliced_par = PC.word ",@" in
         PC.pack (PC.caten unquoted_spliced_par sexpr_parser)
         (fun (a,b) -> Pair(Symbol("unquote-splicing"), Pair(b, Nil)))
         s
    and sexpr_comments_parser s =
        let prefix_par = PC.word "#;" in
        PC.pack (PC.caten prefix_par sexpr_parser) (fun (temp) -> Nil)
        s
    and disj_stars_comments_white_spaces s =
         PC.pack (PC.star (PC.disj sexpr_comments_parser (PC.disj line_comments_parser white_spaces_parser))) (fun(temp) -> Nil)
         s
    and a_parser s =
         pack (caten (disj_stars_comments_white_spaces)
        (caten (PC.disj_list [PC.diff sexpr_parser s_parser; dl_parser; sdl_parser; l_parser; sl_parser; v_parser]) (disj_stars_comments_white_spaces)))
        (function (a,(b,c)) -> b) s
    and s_parser s =
        let three_dots_par = PC.word "..." in
        let s_par = (caten (PC.caten (PC.disj_list [dl_parser; sdl_parser; l_parser; sl_parser; v_parser])disj_stars_comments_white_spaces )three_dots_par) in
        PC.pack s_par (function ((sexp,dots),spaces) -> sexp)
        s
    and l_parser s =
        let open_par = PC.word "(" in
        let close_par = PC.word ")" in
        let l_par = PC.caten open_par (PC.caten (PC.star a_parser) (PC.maybe close_par)) in
        PC.pack l_par (function(a, (lst,b)) -> match lst with
        | [] -> Nil
        | _ -> List.fold_right (fun a b -> Pair(a,b)) lst Nil)
        s
    and sl_parser s =
        let open_par = PC.word "[" in
        let close_par = PC.word "]" in
        let l_par = PC.caten open_par (PC.caten (PC.star a_parser) (PC.maybe close_par)) in
        PC.pack l_par (function(a, (lst,b)) -> match lst with
        | [] -> Nil
        | _ -> List.fold_right (fun a b -> Pair(a,b)) lst Nil)
        s
    and dl_parser s =
        let open_par = PC.word "(" in
        let dot_par = PC.word "." in
        let close_par = PC.word ")" in
        let dl_par = PC.caten open_par (PC.caten (PC.plus a_parser) (PC.caten dot_par (PC.caten a_parser (PC.maybe close_par)))) in
        PC.pack dl_par (function (first, (lst, (dot, (e, last)))) -> match lst with
        | _ -> List.fold_right (fun a b -> Pair(a,b)) lst e)
        s
    and sdl_parser s =
        let open_par = PC.word "[" in
        let dot_par = PC.word "." in
        let close_par = PC.word "]" in
        let dl_par = PC.caten open_par (PC.caten (PC.plus a_parser) (PC.caten dot_par (PC.caten a_parser (PC.maybe close_par)))) in
        PC.pack dl_par (function (first, (lst, (dot, (e, last)))) -> match lst with
        | _ -> List.fold_right (fun a b -> Pair(a,b)) lst e)
        s
    and v_parser s =
        let prefix_par = PC.word "#" in
        let open_par = PC.word "(" in
        let close_par = PC.word ")" in
        let v_par = PC.caten prefix_par (PC.caten open_par (PC.caten (PC.star a_parser) (PC.maybe close_par))) in
        PC.pack v_par (function(a,(b,(lst,c))) -> match lst with
        | _ -> Vector(lst))
        s;;




let read_sexpr string =
    let (e, s) = (sexpr_parser (string_to_list string)) in
    if (s = [])
    then e
    else raise X_no_match;;


let read_sexprs string =
    let (lst, s) = ((PC.star sexpr_parser) (string_to_list string)) in
    lst;;

end;; (* struct Reader *)



