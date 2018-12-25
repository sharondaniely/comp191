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
end;;

module Semantics : SEMANTICS = struct

(*COMMENT *)

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
  
let get_new_counter_ref counter =
    if ((counter := (!counter+1)) = ())
    then counter
    else counter;;

let rec box e =
  match e with
  | Const'(c) -> Const'(c)
  | If'(exp1, exp2, exp3) -> If'((box exp1), (box exp2), (box exp3))
  | Seq'(exp_lst) -> Seq'((List.map (fun (exp) -> (box exp)) exp_lst))
  | Def'(exp1, exp2) -> Def'((box exp1), (box exp2))
  | Set'(exp1, exp2) -> Set'((box exp1), (box exp2))
  | Or'(exp_lst) -> Or'((List.map (fun (exp) -> (box exp)) exp_lst))
  | Var'(v) -> Var'(v)
  | Applic'(exp, exp_lst) -> Applic'((box exp), (List.map (fun (exp1) -> (box exp1)) exp_lst))
  | ApplicTP'(exp, exp_lst) -> ApplicTP'((box exp), (List.map (fun (exp1) -> (box exp1)) exp_lst))
  | LambdaSimple'(str_lst, exp) -> (box_for_lambdas e)
  | LambdaOpt'(str_lst, str, exp) -> (box_for_lambdas e)
  | Box'(v) -> Box'(v)
  | BoxGet'(v) -> BoxGet'(v)
  | BoxSet'(v, exp) -> BoxSet'(v,(box exp))

 and box_for_lambdas lambda =
  match lambda with
   | LambdaSimple'(str_lst, exp) -> 
        (box_lambda_and_send_recursivly lambda (List.map (fun (str) -> (should_be_boxed str exp)) str_lst))
   | LambdaOpt'(str_lst, str, exp) -> 
        (box_lambda_and_send_recursivly lambda (List.map (fun (str1) -> (should_be_boxed str1 exp)) (str_lst@[str])))
   | _ -> raise X_syntax_error
   and should_be_boxed str lambda_body =
    let index1 = {contents = 0} in
    let index2 = {contents = 0} in
    let read_lst = (get_read_lst str lambda_body index1 true true) in
    let write_lst = (get_write_lst str lambda_body index2 true true) in
    let ans_lst1 = (List.map (fun (num) -> (contain_another_num num write_lst)) read_lst) in
    let ans_lst2 = (List.map (fun (num) -> (contain_another_num num read_lst)) write_lst) in
    if ((List.mem true ans_lst1) || (List.mem true ans_lst2))
       then "true"
       else "false"
  and contain_another_num num lst =
    match lst with
  | [] -> false
  | h :: t -> if (num = h) then (contain_another_num num t) else true
  and get_read_lst str exp counter_ref is_first same_str =
    match exp with
  | Const'(c) -> []
  | If'(exp1, exp2, exp3) -> 
      (get_read_lst str exp1 counter_ref is_first same_str)@(get_read_lst str exp2 counter_ref is_first same_str)@(get_read_lst str exp3 counter_ref is_first same_str) 
  | Seq'(exp_lst) ->
    (List.fold_left (fun a b -> List.append a b) [] (List.map (fun (exp1) -> (get_read_lst str exp1 counter_ref is_first same_str))exp_lst)) 
  | Def'(exp1, exp2) -> raise X_syntax_error
  | Set'(Var'(VarBound(str1,index1,index2)),exp1) -> 
     if ((str1 = str) && same_str)
     then (get_read_lst str exp1 counter_ref is_first same_str)
     else (get_read_lst str (Var'(VarBound(str1, index1, index2))) counter_ref is_first same_str)@(get_read_lst str exp1 counter_ref is_first same_str)
  | Set'(Var'(VarParam(str1,index)),exp1) ->  
     if ((str1 = str) && same_str && is_first)
     then (get_read_lst str exp1 counter_ref is_first same_str)
     else (get_read_lst str (Var'(VarParam(str1,index))) counter_ref is_first same_str)@(get_read_lst str exp1 counter_ref is_first same_str)
  | Set'(exp1, exp2) -> 
    (get_read_lst str exp1 counter_ref is_first same_str)@(get_read_lst str exp2 counter_ref is_first same_str)
  | Or'(exp_lst) ->
    (List.fold_left (fun a b -> List.append a b) [] (List.map (fun (exp1) -> (get_read_lst str exp1 counter_ref is_first same_str))exp_lst)) 
  | Var'(VarFree(str1)) -> []
  | Var'(VarBound(str1, index1, index2)) ->
     if ((str = str1) && same_str)
     then [!counter_ref]
     else []
  | Var'(VarParam(str1, index)) ->
    if ((str1 = str) && is_first)
    then [0]
    else []
  | Applic'(exp1, exp_lst) ->
    (get_read_lst str exp1 counter_ref is_first same_str)@(List.fold_left (fun a b -> List.append a b) [] (List.map (fun (exp2) -> (get_read_lst str exp2 counter_ref is_first same_str))exp_lst))
  | ApplicTP'(exp1, exp_lst) -> 
    (get_read_lst str exp1 counter_ref is_first same_str)@(List.fold_left (fun a b -> List.append a b) [] (List.map (fun (exp2) -> (get_read_lst str exp2 counter_ref is_first same_str))exp_lst))
  | LambdaSimple'(str_lst, exp1) -> 
    if is_first
    then (get_read_lst str exp1 (get_new_counter_ref counter_ref) false (not(List.mem str str_lst)))
    else if same_str
         then (get_read_lst str exp1 counter_ref is_first (not(List.mem str str_lst)))
         else (get_read_lst str exp1 counter_ref is_first same_str)
  | LambdaOpt'(str_lst, str1, exp1) -> 
    if is_first
    then (get_read_lst str exp1 (get_new_counter_ref counter_ref) false (not(List.mem str (str_lst@[str1]))))
    else if same_str
         then (get_read_lst str exp1 counter_ref is_first (not(List.mem str (str_lst@[str1]))))
         else (get_read_lst str exp1 counter_ref is_first same_str)
  | Box'(v) -> []
  | BoxGet'(v) -> []
  | BoxSet'(v, exp1) -> (get_read_lst str exp1 counter_ref is_first same_str)
  and get_write_lst str exp counter_ref is_first same_str =
    match exp with
  | Const'(c) -> []
  | If'(exp1, exp2, exp3) -> 
      (get_write_lst str exp1 counter_ref is_first same_str)@(get_write_lst str exp2 counter_ref is_first same_str)@(get_write_lst str exp3 counter_ref is_first same_str) 
  | Seq'(exp_lst) ->
    (List.fold_left (fun a b -> List.append a b) [] (List.map (fun (exp1) -> (get_write_lst str exp1 counter_ref is_first same_str))exp_lst)) 
  | Def'(exp1, exp2) -> raise X_syntax_error
  | Set'(Var'(VarBound(str1,index1,index2)),exp1) -> 
     if ((str = str1) && same_str)
     then [!counter_ref]@(get_write_lst str exp1 counter_ref is_first same_str)
     else (get_write_lst str exp1 counter_ref is_first same_str)
  | Set'(Var'(VarParam(str1,index)),exp1) ->  
    if ((str1 = str) && is_first)
    then [0]@(get_write_lst str exp1 counter_ref is_first same_str)
    else (get_write_lst str exp1 counter_ref is_first same_str)
  | Set'(exp1, exp2) -> 
    (get_write_lst str exp1 counter_ref is_first same_str)@(get_write_lst str exp2 counter_ref is_first same_str)
  | Or'(exp_lst) ->
    (List.fold_left (fun a b -> List.append a b) [] (List.map (fun (exp1) -> (get_write_lst str exp1 counter_ref is_first same_str))exp_lst)) 
  | Var'(var) -> []
  | Applic'(exp1, exp_lst) ->
    (get_write_lst str exp1 counter_ref is_first same_str)@(List.fold_left (fun a b -> List.append a b) [] (List.map (fun (exp2) -> (get_write_lst str exp2 counter_ref is_first same_str))exp_lst))
  | ApplicTP'(exp1, exp_lst) -> 
    (get_write_lst str exp1 counter_ref is_first same_str)@(List.fold_left (fun a b -> List.append a b) [] (List.map (fun (exp2) -> (get_write_lst str exp2 counter_ref is_first same_str))exp_lst))
  | LambdaSimple'(str_lst, exp1) -> 
    if is_first
    then (get_write_lst str exp1 (get_new_counter_ref counter_ref) false (not(List.mem str str_lst)))
    else if same_str
         then (get_write_lst str exp1 counter_ref is_first (not(List.mem str str_lst)))
         else (get_write_lst str exp1 counter_ref is_first same_str)
  | LambdaOpt'(str_lst, str1, exp1) -> 
    if is_first
    then (get_write_lst str exp1 (get_new_counter_ref counter_ref) false (not(List.mem str (str_lst@[str1]))))
    else if same_str
         then (get_write_lst str exp1 counter_ref is_first (not(List.mem str (str_lst@[str1]))))
         else (get_write_lst str exp1 counter_ref is_first same_str)
  | Box'(v) -> []
  | BoxGet'(v) -> []
  | BoxSet'(v, exp1) -> (get_write_lst str exp1 counter_ref is_first same_str) 
  and box_lambda_and_send_recursivly lambda lst =
match lambda with
   | LambdaSimple'(str_lst, exp) -> 
      let first_changed_body = (new_body exp str_lst lst) in
      let addition_to_body = Seq'((body_begin str_lst str_lst lst)) in
      let second_changed_body = (newbody2 first_changed_body addition_to_body) in
      LambdaSimple'(str_lst, (box second_changed_body))
   | LambdaOpt'(str_lst, str, exp) -> 
      let first_changed_body = (new_body exp (str_lst@[str]) lst) in
      let addition_to_body = Seq'((body_begin (str_lst@[str]) (str_lst@[str]) lst)) in
      let second_changed_body = (newbody2 first_changed_body addition_to_body) in
      LambdaOpt'(str_lst,str, (box second_changed_body))
   | _ -> raise X_syntax_error
  and newbody2 body begin_body =
  match begin_body with
  | Seq'([]) -> body
  | Seq'(exp_lst) -> Seq'(exp_lst@[body])
  | _ -> raise X_syntax_error
  and body_begin original_arg_lst arg_lst should_be_boxed_lst =
   match should_be_boxed_lst with
  | [] -> []
  | h :: t -> if (h = "true")
              then ([Set'(Var'(VarParam((List.hd arg_lst),(index_in_lst (List.hd arg_lst) original_arg_lst))),Box'(VarParam((List.hd arg_lst), (index_in_lst (List.hd arg_lst) original_arg_lst))))]@(body_begin original_arg_lst (List.tl arg_lst) t))
              else (body_begin original_arg_lst (List.tl arg_lst) t)
  and new_body old_body arg_lst should_be_boxed_lst =
   match should_be_boxed_lst with
   | [] -> old_body
   | h :: t -> if (h = "true")
               then (new_body (change_body (List.hd arg_lst) old_body true) (List.tl arg_lst) t)
               else (new_body old_body (List.tl arg_lst) t)
  and index_in_lst str lst =
   match lst with
    | [] -> raise X_syntax_error
    | h :: t -> if str = h then 0 else 1 + (index_in_lst str t)
  and change_body str old_body same_str=
   match old_body with
  | Const'(c) -> Const'(c)
  | If'(exp1, exp2, exp3) -> 
     If'((change_body str exp1 same_str),(change_body str exp2 same_str), (change_body str exp3 same_str)) 
  | Seq'(exp_lst) ->
     Seq'((List.map (fun (exp1) -> (change_body str exp1 same_str))exp_lst)) 
  | Def'(exp1, exp2) -> raise X_syntax_error
  | Set'(Var'(VarBound(str1,index1,index2)),exp1) -> 
    if ((str = str1) && same_str)
    then BoxSet'(VarBound(str1,index1,index2),(change_body str exp1 same_str))
    else Set'(Var'(VarBound(str1,index1,index2)),(change_body str exp1 same_str))
  | Set'(Var'(VarParam(str1,index)),exp1) ->
    if ((str1 = str) && same_str)
    then (BoxSet'(VarParam(str1,index),(change_body str exp1 same_str)))
    else (Set'(Var'(VarParam(str1,index)),(change_body str exp1 same_str)))
  | Set'(exp1, exp2) -> 
    Set'((change_body str exp1 same_str), (change_body str exp2 same_str))
  | Or'(exp_lst) ->
     Or'((List.map (fun (exp1) -> (change_body str exp1 same_str))exp_lst))
  | Var'(VarFree(str1)) -> Var'(VarFree(str1))
  | Var'(VarBound(str1, index1, index2)) ->
    if ((str = str1) && same_str)
    then BoxGet'(VarBound(str1, index1, index2))
    else Var'(VarBound(str1, index1, index2)) 
  | Var'(VarParam(str1, index)) ->
    if ((str1 = str) && same_str)
    then BoxGet'(VarParam(str1, index))
    else Var'(VarParam(str1,index))
  | Applic'(exp1, exp_lst) ->
     Applic'((change_body str exp1 same_str), (List.map (fun (exp2) -> (change_body str exp2 same_str))exp_lst))
  | ApplicTP'(exp1, exp_lst) -> 
     ApplicTP'((change_body str exp1 same_str), (List.map (fun (exp2) -> (change_body str exp2 same_str))exp_lst))
  | LambdaSimple'(str_lst, exp1) -> 
    if same_str
    then LambdaSimple'(str_lst, (change_body str exp1 (not(List.mem str str_lst))))
    else LambdaSimple'(str_lst, (change_body str exp1 same_str))
  | LambdaOpt'(str_lst, str1, exp1) -> 
    if same_str
    then LambdaOpt'(str_lst, str1, (change_body str exp1 (not(List.mem str (str_lst@[str1])))))
    else LambdaOpt'(str_lst, str1, (change_body str exp1 same_str))
  | Box'(v) -> Box'(v)
  | BoxGet'(v) -> BoxGet'(v)
  | BoxSet'(v, exp1) -> BoxSet'(v,(change_body str exp1 same_str))

  
let rec tail_calls e in_tp =
  match e with
  | Const'(exp)-> Const'(exp)
  | If' (exp1 , exp2, exp3) ->  If'( (tail_calls exp1 false) , (tail_calls exp2 in_tp) , (tail_calls exp3 in_tp))
  | Seq' (expr_lst) ->  Seq' ((List.map (fun (elm)-> (tail_calls elm false)) (list_excepte_last expr_lst))@ [(tail_calls (list_last_element expr_lst) in_tp)]) 
  | Def' (exp1 , exp2) -> Def' ((tail_calls exp1 in_tp), (tail_calls exp2 in_tp))
  | Set' (exp1 , exp2) -> Set' ((tail_calls exp1 in_tp), (tail_calls exp2 false))
  | Or' (expr_lst)-> Or' (  (List.map (fun (elm)-> (tail_calls elm false)) (list_excepte_last expr_lst))@[(tail_calls (list_last_element expr_lst) in_tp)]) 
  | LambdaSimple' (vars, exp)-> LambdaSimple' (vars, (tail_calls exp true))
  | LambdaOpt' (str_lst, str, exp)-> LambdaOpt'(str_lst, str , (tail_calls exp true))
  | Var' (var) -> Var' (var) 
  | Applic'(exp, exp_lst)-> if in_tp 
                                then ApplicTP'((tail_calls exp false), (List.map (fun (elm)-> (tail_calls elm false)) exp_lst ))
                                else Applic'((tail_calls exp false), (List.map (fun (elm)-> (tail_calls elm false))  exp_lst))
  |_-> raise X_syntax_error                              
  and list_last_element lst =  (List.hd (List.rev lst))
  and list_excepte_last lst= (List.rev (List.tl (List. rev lst)))
  ;;


let annotate_lexical_addresses e = (lexical e [] []) ;;
 
let annotate_tail_calls e = (tail_calls e false);;



let box_set e = (box e) ;;


let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
