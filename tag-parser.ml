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
  val expr_parser : sexpr -> expr
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



let rec expr_parser s =
  match s with
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | Number(x) -> Const(Sexpr(Number(x)))
  | String(x) -> Const(Sexpr(String(x)))
  | Pair(Symbol("quote") , Pair(x , Nil)) -> Const(Sexpr(x))
  | Pair(Symbol("unquote") , Pair(x , Nil)) -> Const(Sexpr(x)) (*TODO CHECK WHAT TODO HERE*)
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(expr_parser test, expr_parser dit, Const(Void))
  | Pair(Symbol("if"), Pair(test , Pair(dit , Pair(dif , Nil)))) -> If(expr_parser test, expr_parser dit, expr_parser dif)
  | Symbol(x) -> if (List.mem x reserved_word_list)
                then raise X_syntax_error
                else Var(x)
  | Pair(Symbol("define") , Pair(name , Pair(expr , Nil))) -> Def(expr_parser name , expr_parser expr)
  | Pair(Symbol("set!") , Pair(name , Pair(expr , Nil))) -> Set(expr_parser name, expr_parser expr)
  | Pair(Symbol("or"), x) -> (or_expr_parser x)
  | Pair(Symbol("begin"), x) -> (begin_expr_parser x)
  | Pair(Symbol("cond"), x) -> (cond_expr_parser x) (*TODO WRITE THIS FUNCTION*)
  | Pair(Symbol("let"), x) -> (expr_let_parser x) (*TODO WRITE THIS FUNCTION*)
  | Pair(Symbol("let*"), x) -> (expr_let_star_parser x) (*TODO WRITE THIS FUNCTION*)
  | Pair(Symbol("letrec"), x) -> (expr_letrec_parser x) (*TODO WRITE THIS FUNCTION*)
  | Pair(Symbol("lambda"), x) -> (lambda_expr_parser x) (*TODO WRITE THIS FUNCTION*) 
  | Pair(Symbol("and"), x) -> (and_expr_parser x) (*TODO WRITE THIS FUNCTION*)
  | Pair(Symbol("quasiquote"), Pair(x , Nil)) -> (quasiquote_expr_parser x) (*TODO WRITE THIS FUNCTION*)
  | Pair(a , b) -> Applic((expr_parser a) , nested_pair_sexpr_to_list(b))
  | _ -> raise X_syntax_error
 and or_expr_parser x =
  match x with
  | Nil -> Const(Sexpr(Bool(false)))
  | Pair(y , Nil) -> (expr_parser y)
  | _ -> Or((nested_pair_sexpr_to_list x))
 and begin_expr_parser x =
  match x with
  | Nil -> Const(Void)
  | Pair(y , Nil) -> (expr_parser y)
  | _ -> Seq((nested_pair_sexpr_to_list x))
 and nested_pair_sexpr_to_list x =
  match x with
  | Nil -> []
  | Pair(a,b) -> List.append [(expr_parser a)] (nested_pair_sexpr_to_list b)
  | _ -> [(expr_parser x)];;

  
end;; (* struct Tag_Parser *)