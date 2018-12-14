(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val get_read_lst : string -> expr' -> int -> bool -> bool -> int list (*TODO DON'T FORGET TO REMOVE *)
end;;

module Semantics : SEMANTICS = struct



let rec lexical e plst blst =
  match e with
  | Const(c) -> Const'(c)
  | If(exp1, exp2, exp3) -> If'((lexical exp1 plst blst), (lexical exp2 plst blst), (lexical exp3 plst blst))
  | Seq(exp_lst) -> Seq'((List.map (fun (exp) -> (lexical exp plst blst)) exp_lst))
  | Def(exp1, exp2) -> Def'((lexical exp1 plst blst), (lexical exp2 plst blst))
  | Set(exp1, exp2) -> Set'((lexical exp1 plst blst), (lexical exp2 plst blst))
  | Or(expr_lst) -> Or'((List.map (fun (exp) -> (lexical exp plst blst)) expr_lst))
  | Applic(exp, expr_lst) -> Applic'((lexical exp plst blst), (List.map (fun (exp1)-> (lexical exp1 plst blst)) expr_lst))
  | LambdaSimple(str_lst, exp) -> LambdaSimple'(str_lst, (lexical exp str_lst (plst::blst)))
  | LambdaOpt(str_lst, str, exp) -> LambdaOpt'(str_lst, str, (lexical exp (str_lst@[str]) (plst::blst)))
  | Var(str) -> if (List.mem str plst)
                then Var'(VarParam(str, (index_in_lst str plst)))
                else (bound_or_free str blst 0)
 and index_in_lst str lst =
  match lst with
    | [] -> raise X_syntax_error
    | h :: t -> if str = h then 0 else 1 + (index_in_lst str t)
 and bound_or_free str lst index=
  match lst with
  | [] -> Var'(VarFree(str))
  | h :: t -> if (List.mem str h) then Var'(VarBound(str, index, (index_in_lst str h))) else (bound_or_free str t (index+1));; 
  


let rec box e =
  match e with
  | Const'(c) -> Const'(c)
  | If'(exp1, exp2, exp3) -> If'((box exp1), (box exp2), (box exp3))
  | Seq'(exp_lst) -> Seq'((List.map (fun (exp) -> (box exp)) exp_lst))
  | Def'(exp1, exp2) -> Def'((box exp1), (box exp2))
  | Set'(exp1, exp2) -> Set'((box exp1), (box exp2))
  | Or'(exp_lst) -> Or'((List.map (fun (exp) -> (box exp)) exp_lst))
  | Var'(var) -> Var'(var)
  | Applic'(exp, exp_lst) -> Applic'((box exp), (List.map (fun (exp1) -> (box exp1)) exp_lst))
  | ApplicTP'(exp, exp_lst) -> ApplicTP'((box exp), (List.map (fun (exp1) -> (box exp1)) exp_lst))
  | LambdaSimple'(str_lst, exp) -> (box_for_lambdas e)
  | LambdaOpt'(str_lst, str, exp) -> (box_for_lambdas e)
  (* TODO WOULD PROBABLY NEED TO DEAL WITH BOX SET BOX GET AND BOX PROBABLY LEAVE THEM THE SAME*)
  | _ -> raise X_syntax_error
 and box_for_lambdas lambda =
   raise X_syntax_error;;
                                        


(*let rec tail_calls e in_tp =
  match e with
  | Const'(e)-> Const'(e)
  | If' (exp1 , exp2, exp3) ->  If'( (tail_calls exp1 false) , (tail_calls exp2 in_tp) , (tail_calls exp3 in_tp))
  | Seq' (expr_lst) ->  Seq' ((List.map (fun (elm)-> (tail_calls elm false)) (list_excepte_last expr_lst))@ [(tail_calls (list_last_element expr_lst) in_tp)]) 
  | Def' (exp1 , exp2) -> Def' ((tail_calls exp1 in_tp), (tail_calls exp2 in_tp))
  | Or' (expr_lst)-> Or' (  (List.map (fun (elm)-> (tail_calls elm false)) (list_excepte_last expr_lst))@[(tail_calls (list_last_element expr_lst) in_tp)]) 
  | LambdaSimple' (vars, exp)-> LambdaSimple' (vars, (tail_calls exp true))
  | LambdaOpt' (str_lst, str, exp)-> LambdaOpt'(str_lst, str , (tail_calls exp true))
  | Var' (str) -> Var' (str) (*TODO do we need to add var to tjis function*)
  | Applic'(exp, exp_lst)-> if in_tp 
                                then ApplicTP'((tail_calls exp in_tp), (List.map (fun (elm)-> (tail_calls elm false)) (list_excepte_last exp_lst))@[(tail_calls (list_last_element exp_lst) in_tp)])
                                else Applic'((tail_calls exp in_tp), (List.map (fun (elm)-> (tail_calls elm false)) (list_excepte_last exp_lst))@[(tail_calls (list_last_element exp_lst) in_tp)])
  |_-> raise X_syntax_error                              
 

  and list_last_element lst =
  match lst with
  | [] -> 
  | _ -> (List.hd (List.rev lst))
  and list_excepte_last lst=
  match lst with
  | []-> Nil
  | _-> (List.rev (List.tl (List. rev lst)))
  ;;
*)

let annotate_lexical_addresses e = (lexical e [] []) ;;
 
(*let annotate_tail_calls e = (tail_calls e false);;*)

let annotate_tail_calls e = raise X_syntax_error;; (* TODO DON'T FORGET TO DELETE *)

let box_set e = (box e);;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
