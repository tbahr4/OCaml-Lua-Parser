open List
open Float

type ident = string
type num = Integer of int | Float of float


(* type checker *)
type typ = NumTy | BooleanTy | StringTy | NilTy | TableTy


(* Expressions *)
type exp = Var of ident     (* x *)
        | Number of num     (* Numbers may be float or int *)
        | Boolean of bool   (* Note: types are implied *)
        | String of string  (* Note: types are implied *)
        | Nil               (* nil *)
        | Table of ident    (* x *)
        | Add of exp * exp  (* a + b *)
        | Mul of exp * exp  (* a * b *)
        | Sub of exp * exp  (* a - b *)
        | Div of exp * exp  (* a / b *)
        | Eq of exp * exp   (* a = b *)
        | And of exp * exp  (* a and b *)
        | Or of exp * exp   (* a or b *)
        | TableGet of ident * exp               (* arr[4], arr[3.4], arr['str'], arr[3+4] *)


        
(* Commands *)
type cmd = Assign of ident * exp
        | Seq of cmd * cmd
        | Skip
        | IfElse of exp * cmd * cmd
        | While of exp * cmd
        | Call of ident * ident * exp list
        | Return of exp
        | DefineTable of ident                  (* arr = {} *)          
        | TableSet of ident * exp * exp         (* arr["key"] = 2.3 *)



(* Defines a current context of types *)
type context = ident -> typ option
let empty_context = fun x -> None

(* Lookup ident's type in current context *)
let lookup (gamma : context) (x : ident) : typ option = gamma x



(* Returns the type of the given expression in the current context *)
let rec type_of (gamma : context) (e : exp) : typ option =
        match e with
        | Var x -> lookup gamma x
        | Number n -> Some NumTy
        | Boolean b -> Some BooleanTy
        | String s -> Some StringTy
        | Nil -> Some NilTy
        | Table i -> Some TableTy
        | Add (e1,e2) | Sub (e1,e2) | Mul (e1,e2) | Div (e1,e2) -> 
                (match type_of gamma e1, type_of gamma e2 with
                 | Some NumTy, Some NumTy -> Some NumTy
                 | _, _ -> None)       (* Cannot perform arithmetic on Strings, Booleans, Tables, or nil *)
        | Eq (e1,e2) | And (e1,e2) | Or (e1,e2) -> 
                (match type_of gamma e1, type_of gamma e2 with
                 | Some t1, Some t2 -> Some BooleanTy   (* All types are comparable *)
                 | _, _ -> None)
        | TableGet (i,e) -> None     (* Any expr type is allowed as a table key, except Nil *)      
                
                (*  ^^^^^  *)
                (* Not sure, store with list or separately? or easier way *)

        
   

        
(* Returns true if the given command is type correct *)
let rec typecheck_cmd (gamma : context) (c : cmd) : bool =
        match c with
        | Assign (i,e) ->       (* Variable types are implied, and can be changed anytime *)
                (match lookup gamma i, type_of gamma e with
                 | Some t1, Some t2 -> true
                 | _, _ -> false)
        | Seq (c1,c2) -> typecheck_cmd gamma c1 && typecheck_cmd gamma c2
        | Skip -> true
        | IfElse (e,c1,c2) -> type_of gamma e = Some BooleanTy && typecheck_cmd gamma c1 && typecheck_cmd gamma c2
        | While (e,c) -> type_of gamma e = Some BooleanTy && typecheck_cmd gamma c
        (*| Call of (i1,i2,eList)*)
        (*| Return of *)
        | TableSet (i,e1,e2) -> (match (type_of gamma e1) with        
                                 | Some NilTy -> false      (* Any expr type is allowed as a table key, except Nil *)
                                 | Some _ -> true           (* Table value can be ANY type, even nil *)
                                 | None -> false
                                 )
        | DefineTable i -> true         (* Table can have any name, may also overwrite other vars *)
        | _ -> false




(* semantics *)
type value = NumVal of num | BooleanVal of bool | StringVal of string | NilVal | TableVal of (value * value) list
   
            (*              fun (list of params) { cmd }  *)
type entry = Val of value | Fun of ident list * cmd

type state = ident -> entry option
let empty_state = fun x -> None
let lookup (s : state) (x : ident) : entry option = s x
let update (s : state) (x : ident) (e : entry) : state = fun y -> if y = x then Some e else s y




(* Retrieves the element from the table if it exists, or Nil if not *)
let rec get_table (t:(value * value) list) (v:value) : value =
        match t with
        | [] -> NilVal             (* Not found, return Nil *)
        | (headKey, headVal)::tail when headKey = v -> headVal        (* found, return value *)
        | (headKey, headVal)::tail -> get_table tail v                (* Not found, continue down list *)
        



let rec eval_exp (e : exp) (s : state) : value option =
        match e with
        | Var x -> (match lookup s x with
                    | Some (Val v) -> Some v
                    | _ -> None)
        | Number n -> Some (NumVal n)      
        | Boolean b -> Some (BooleanVal b)
        | String s -> Some (StringVal s)
        | Nil -> Some NilVal
        | Table i -> (match lookup s i with
                      | Some (Val TableVal t) -> Some (TableVal t)                                     
                      | _ -> None
                     )
        | Add (e1,e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (NumVal i1), Some (NumVal i2) -> (match (i1,i2) with
                                                                   | (Integer ii1, Integer ii2) -> Some (NumVal (Integer (ii1+ii2))) 
                                                                   | (Float f1, Float f2) ->       Some (NumVal (Float (add f1 f2))) 
                                                                   | (Integer ii1, Float f1) ->    Some (NumVal (Float (add (float_of_int ii1) f1))) 
                                                                   | (Float f1, Integer ii1) ->    Some (NumVal (Float (add (float_of_int ii1) f1))) 
                                                                   )
                          | _, _ -> None)
        | Mul (e1,e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (NumVal i1), Some (NumVal i2) -> (match (i1,i2) with
                                                                  | (Integer ii1, Integer ii2) -> Some (NumVal (Integer (ii1*ii2))) 
                                                                  | (Float f1, Float f2) ->       Some (NumVal (Float (mul f1 f2))) 
                                                                  | (Integer ii1, Float f1) ->    Some (NumVal (Float (mul (float_of_int ii1) f1))) 
                                                                  | (Float f1, Integer ii1) ->    Some (NumVal (Float (mul (float_of_int ii1) f1))) 
                                                                  )
                          | _, _ -> None)
        | Sub (e1,e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (NumVal i1), Some (NumVal i2) -> (match (i1,i2) with
                                                                  | (Integer ii1, Integer ii2) -> Some (NumVal (Integer (ii1-ii2))) 
                                                                  | (Float f1, Float f2) ->       Some (NumVal (Float (sub f1 f2))) 
                                                                  | (Integer ii1, Float f1) ->    Some (NumVal (Float (sub (float_of_int ii1) f1))) 
                                                                  | (Float f1, Integer ii1) ->    Some (NumVal (Float (sub (float_of_int ii1) f1))) 
                                                                  )
                          | _, _ -> None)
        | Div (e1,e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (NumVal i1), Some (NumVal i2) -> (match (i1,i2) with
                                                                  | (Integer ii1, Integer ii2) -> Some (NumVal (Integer (ii1/ii2))) 
                                                                  | (Float f1, Float f2) ->       Some (NumVal (Float (div f1 f2))) 
                                                                  | (Integer ii1, Float f1) ->    Some (NumVal (Float (div (float_of_int ii1) f1))) 
                                                                  | (Float f1, Integer ii1) ->    Some (NumVal (Float (div (float_of_int ii1) f1))) 
                                                                  )
                          | _, _ -> None)
        | Eq (e1,e2) -> (match eval_exp e1 s, eval_exp e2 s with
                         | Some v1, Some v2 -> Some (BooleanVal (v1 = v2))
                         | _, _ -> None)
        | And (e1,e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (BooleanVal b1), Some (BooleanVal b2) -> Some (BooleanVal (b1 && b2))
                          | _, _ -> None)
        | Or (e1,e2) -> (match eval_exp e1 s, eval_exp e2 s with
                         | Some (BooleanVal b1), Some (BooleanVal b2) -> Some (BooleanVal (b1 || b2))
                         | _, _ -> None)
        | TableGet (i,e) ->(match lookup s i with               (* Get the table, then search it *)
                            | Some (Val TableVal t) -> (match eval_exp e s with
                                                        | Some v -> if v = NilVal then None else Some (get_table t v)
                                                        | _ -> None
                                                       )
                            | _ -> None 
                           )               
                            



let rec eval_exps (es : exp list) (s : state) : value list option =
match es with
| [] -> Some []
| e :: rest -> (match eval_exp e s, eval_exps rest s with
                | Some v, Some vs -> Some (v :: vs)
                | _, _ -> None)

let rec add_args (s : state) (li : ident list) (lv : value list) : state =
        match li, lv with
        | i :: irest, v :: vrest -> add_args (update s i (Val v)) irest vrest
        | _, _ -> s
       
        
type stack = (state * ident) list

type config = cmd * stack * state







(* Adds element to table or replaces it; t[e1] = e2 *)                  
(* t -> list of (key, value) *)
let rec set_table_helper t (v1:value) (v2:value) (final:(value * value) list) =
        match t with
        | [] -> final @ [(v1,v2)]         (* Not found; add to list without replacement *)
        | (headKey, headVal)::tail when (headKey = v1) && (v2 = NilVal) -> final @ tail                 (* Matched when value = Nil; remove value and add rest of list *)
        | (headKey, headVal)::tail when (headKey = v1) -> let new_final = final @ [(v1,v2)] in          (* Matched; overwrite value and add rest of list *)
                                                          new_final @ tail      
        | head::tail -> set_table_helper tail v1 v2 final @ [head]      (* Not matched; add head to final and continue *)

let set_table t (v1:value) (v2:value) =         
        (* If nil key, do not add *)
        if v1 = NilVal then 
                t 
        else
                let new_table = set_table_helper t v1 v2 [] in
                new_table       (* ret new table *)


                


let rec step_cmd (c : cmd) (k : stack) (s : state) : config option =
        match c with
        | Assign (x, e) -> (match eval_exp e s with
                            | Some v -> Some (Skip, k, update s x (Val v))
                            | None -> None)
        | Seq (Skip, c2) -> Some (c2, k, s)
        | Seq (c1, c2) -> (match step_cmd c1 k s with
                        | Some (c1', k', s') -> Some (Seq (c1', c2), k', s')
                        | None -> None)
        | Skip -> None
        | IfElse (e, c1, c2) -> (match eval_exp e s with
                                | Some (BooleanVal true) -> Some (c1, k, s)
                                | Some (BooleanVal false) -> Some (c2, k, s)
                                | _ -> None)
        | While (e, c) -> Some (IfElse (e, Seq (c, While (e, c)), Skip), k, s)
        | Call (x, f, es) -> (match eval_exps es s with
                                | Some vs -> (match lookup s f with
                                                | Some (Fun (params, c)) -> Some (c, (s, x) :: k, add_args s params vs)
                                                | _ -> None)
                                | None -> None)
        | Return e -> (match eval_exp e s, k with
                        | Some v, (s', x) :: k' -> Some (Skip, k', update s' x (Val v))
                        | _, _ -> None)
        | TableSet (i,e1,e2) -> (match lookup s i with          (* could have used eval_exp instead *)
                                 | Some (Val TableVal t) -> (match (eval_exp e1 s, eval_exp e2 s) with
                                                             | Some v1, Some v2 -> if v1 = NilVal then None else let new_table = (set_table t v1 v2) in   (* Add t[e1] = e2 *)
                                                                                                                 Some (Skip, k, update s i (Val (TableVal new_table)))
                                                             | _, _ -> None
                                                            )
                                 | _ -> None
                                )
        | DefineTable i -> Some (Skip, k, update s i (Val (TableVal [])))       (* Define table to initially be empty *)
(*
        let a:entry = Val (BooleanVal true)
        let b = update empty_state "x" a
*)

let rec run_config (con : config) : config =
        let (c, k, s) = con in
        match step_cmd c k s with
        | Some con' -> run_config con'
        | None -> con
        
let run_prog (c : cmd) s =
run_config (c, [], s)
        
        
        


(* Test DefineTable *)
let config1 = (DefineTable "tab", [], empty_state)
let (res_c, res_k, res_s) = run_config config1;;
let l = lookup res_s "tab"

(* Test SetTable *)
let tSet1 = TableSet ("tab", Number (Integer 1), Number (Integer 50)) 
let tSet2 = TableSet ("tab", Number (Integer 2), Number (Float 2.5))
let tSet3 = TableSet ("tab", String "test", Boolean true)
let tSet4 = TableSet ("tab", Number (Integer 1), Nil) 
let tSet5 = TableSet ("tab", Nil, Number (Float 3.4)) 
let config2 = (tSet1, res_k, res_s)
let (res_c, res_k, res_s) = run_config config2;;
let l2 = lookup res_s "tab"

;;print_endline "\n\n\n\n\n\n\n"

let (res_c, res_k, res_s) = run_config (tSet2, res_k, res_s)
let l3 = lookup res_s "tab"
let (res_c, res_k, res_s) = run_config (tSet3, res_k, res_s)
let l3 = lookup res_s "tab"

(* Test SetTable for Nil Value (removes value from table) *)
;;print_endline "\n\nNil value:"
let (res_c, res_k, res_s) = run_config (tSet4, res_k, res_s)
let l3 = lookup res_s "tab"

(* Test SetTable for Nil key (should not add to table) *)
;;print_endline "\n\nNil key:"
let (res_c, res_k, res_s) = run_config (tSet5, res_k, res_s)
let l3 = lookup res_s "tab"


(* Test eval_exp *)
;;print_endline "\n\nTesting eval_exp for table:"
let evalTab = eval_exp (Table "tab") res_s



(* Test GetTable *)
;;print_endline "\n\nTest GetTable:"
let tGet1 = TableGet ("tab", String "test")

let l = eval_exp tGet1 res_s


(* Test Redefinition of table *)