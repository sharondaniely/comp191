(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
  val expr_parser : sexpr -> expr (*TODO DON'T FORGET TO REMOVE*)
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let tag_parse_expression sexpr = raise X_not_yet_implemented;;

let tag_parse_expressions sexpr = raise X_not_yet_implemented;;

(*TODO DON'T FORGET TO CHECK THERE ARE UNIQE NAMES FOR ARGS - LAMBDA*)
(*TODO TAKE CARE OF UNQUOTE ONLY INSIDE QUASIQOUTE*)

let rec expr_parser s =
  match s with
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | Number(x) -> Const(Sexpr(Number(x)))
  | String(x) -> Const(Sexpr(String(x)))
  | Pair(Symbol("quote") , Pair(x , Nil)) -> Const(Sexpr(x))
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(expr_parser test, expr_parser dit, Const(Void))
  | Pair(Symbol("if"), Pair(test , Pair(dit , Pair(dif , Nil)))) -> If(expr_parser test, expr_parser dit, expr_parser dif)
  | Symbol(x) -> if (List.mem x reserved_word_list)
                then raise X_syntax_error
                else Var(x)
  | Pair(Symbol("define") , Pair(name , Pair(expr , Nil))) -> Def(expr_parser name , expr_parser expr)
  | Pair(Symbol("set!") , Pair(name , Pair(expr , Nil))) -> Set(expr_parser name, expr_parser expr)
  | Pair(Symbol("or"), x) -> (or_expr_parser x)
  | Pair(Symbol("begin"), x) -> (begin_expr_parser x)
  | Pair(Symbol("lambda"), Pair(Symbol(arg), Pair(body,Nil))) -> (lambda_variadic_expr_parser s)
  | Pair(Symbol("lambda"),Pair(args, Pair(body, Nil))) -> if ((not_dotted args) && (not_dotted body))
                                                         then (lambda_simple_expr_parser s)
                                                         else if ((not(not_dotted args)) && (not_dotted body))
                                                              then (lambda_opt_expr_parser s)
                                                              else raise X_syntax_error
  (*| Pair(Symbol("cond"), x) -> (cond_expr_parser x) (*TODO WRITE THIS FUNCTION*)*)
  | Pair(Symbol("let"), x) -> (expr_let_parser s)
  | Pair(Symbol("let*"), x) -> (expr_let_star_parser s) (*TODO WRITE THIS FUNCTION*)
  (*| Pair(Symbol("letrec"), x) -> (expr_letrec_parser x) (*TODO WRITE THIS FUNCTION*)*)
  | Pair(Symbol("and"), x) -> (and_expr_parser x)
  (*| Pair(Symbol("quasiquote"), Pair(x , Nil)) -> (quasiquote_expr_parser x) (*TODO WRITE THIS FUNCTION*)
  MIT Define TODO *)
  | Pair(a , b) -> Applic((expr_parser a) , (nested_pair_sexpr_to_list b))
  | _ -> raise X_syntax_error
 and or_expr_parser x =
  match x with
  | Nil -> Const(Sexpr(Bool(false)))
  | Pair(y , Nil) -> (expr_parser y)
  | _ -> Or((nested_pair_sexpr_to_list x))
 and and_expr_parser x =
  match x with
  | Nil -> Const(Sexpr(Bool(true)))
  | Pair(y , Nil) -> (expr_parser y)
  | Pair(y , z) -> If((expr_parser y), (and_expr_parser z), Const(Sexpr(Bool(false))))
  | _ -> raise X_syntax_error 
 and begin_expr_parser x =
  match x with
  | Nil -> Const(Void)
  | Pair(y , Nil) -> (expr_parser y)
  | _ -> Seq((nested_pair_sexpr_to_list x))
 and lambda_variadic_expr_parser s =
  match s with
  | Pair(Symbol("lambda"), Pair(Symbol(arg), Pair(body,Nil))) -> 
       LambdaOpt([],arg, Seq((nested_pair_sexpr_to_list body)))
  | _ -> raise X_syntax_error
 and lambda_simple_expr_parser s =
  match s with
  | Pair(Symbol("lambda"),Pair(args, Pair(body, Nil))) -> 
      LambdaSimple((sexpr_list_to_string_list args) , Seq((nested_pair_sexpr_to_list body)))
  | _ -> raise X_syntax_error
 and lambda_opt_expr_parser s =
  match s with
  | Pair(Symbol("lambda"),Pair(args, Pair(body, Nil))) -> 
      LambdaOpt((without_last_arg args),(symbol_to_string(last_arg args)), Seq((nested_pair_sexpr_to_list body)))
  | _ -> raise X_syntax_error
 and expr_let_parser s =
  match s with
  | Pair(Symbol("let"),Pair(args_list,body)) -> 
     Applic(LambdaSimple((extract_vars_from_args args_list), Seq((nested_pair_sexpr_to_list body))),(extract_values_from_args args_list))
  | _ -> raise X_syntax_error
 and expr_let_star_parser s =
  match s with
  | Pair(Symbol("let*"), Pair(Nil, body)) -> 
     (expr_parser (Pair(Symbol("let"), Pair(Nil, body))))
  | Pair(Symbol("let*"), Pair(Pair(arg,Nil), body)) -> 
     (expr_parser (Pair(Symbol("let"), Pair(Pair(arg,Nil), body))))
  | Pair(Symbol("let*"), Pair(Pair(head,tail), body)) -> 
     (expr_parser (Pair(Symbol("let"),Pair(Pair(head,Nil), Pair(Pair(Symbol("let*"),Pair(tail, body)),Nil)))))
  | _ -> raise X_syntax_error
 and extract_vars_from_args args_list =
  match args_list with
  | Pair(Pair(Symbol(x),a),b) -> List.append [x] (extract_vars_from_args b)
  | _ -> []
 and extract_values_from_args args_list =
  match args_list with
  | Pair(Pair(Symbol(x),Pair(a,Nil)), b) -> List.append [(expr_parser a)] (extract_values_from_args b)
  | _ -> []
 and sexpr_list_to_string_list x =
  match x with
  | Nil -> []
  | Pair(Symbol(a),b) -> List.append [a] (sexpr_list_to_string_list b)
  | _ -> raise X_syntax_error
 and symbol_to_string x =
  match x with
  | Symbol(a) -> a
  | _ -> raise X_syntax_error
 and not_dotted lst =
  match lst with
  | Nil -> true
  | Pair(a,b) -> (not_dotted b)
  | _ -> false
 and last_arg lst =
  match lst with
  | Pair(a, b) -> (last_arg b)
  | _ -> lst
 and without_last_arg lst =
  match lst with
  | Pair(Symbol(x), Pair(a,b)) -> List.append [x] (without_last_arg (Pair(a,b)))
  | Pair(Symbol(a),b) -> [a]
  | _ -> raise X_syntax_error
 and nested_pair_sexpr_to_list x =
  match x with
  | Nil -> []
  | Pair(a,b) -> List.append [(expr_parser a)] (nested_pair_sexpr_to_list b)
  | _ -> [(expr_parser x)];;

  (*Last comment Adi*)
end;; (* struct Tag_Parser *)
