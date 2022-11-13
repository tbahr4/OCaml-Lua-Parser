open List

type ident = string
type num = Integer of int | Float of float


(* type checker *)
type typ = NumTy | BooleanTy | StringTy | NilTy | TableTy


(* Expressions *)
type exp = Var of ident     (* x *)
        | Number of num     (* Numbers may be float or int *)
        | Boolean of bool   (* Note: types are implied *)
        | String of string  (* Note: types are implied *)
        | Table of ident    (* x *)
        | Add of exp * exp  (* a + b *)
        | Mul of exp * exp  (* a * b *)
        | Sub of exp * exp  (* a - b *)
        | Div of exp * exp  (* a / b *)
        | Eq of exp * exp   (* a = b *)
        | And of exp * exp  (* a and b *)
        | Or of exp * exp   (* a or b *)


(* Commands *)
type cmd = Assign of ident * exp
        | Seq of cmd * cmd
        | Skip
        | IfElse of exp * cmd * cmd
        | While of exp * cmd
        | Call of ident * ident * exp list
        | Return of exp
        | TableLookup of ident * exp    



(* Defines a current context *)
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
        | Table i -> Some TableTy
        | Add (e1,e2) | Sub (e1,e2) | Mul (e1,e2) | Div (e1,e2) -> 
                (match type_of gamma e1, type_of gamma e2 with
                 | Some NumTy, Some NumTy -> Some NumTy
                 | _, _ -> None)       (* Cannot perform arithmetic on Strings, Booleans, Tables, or nil *)
        | Eq (e1,e2) | And (e1,e2) | Or (e1,e2) -> 
                (match type_of gamma e1, type_of gamma e2 with
                 | Some t1, Some t2 -> Some BooleanTy   (* All types are comparable *)
                 | _, _ -> None)
        
        
        
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
        (*| TableLookup of ident * exp                                          TODO *)
        | _ -> false




(* semantics *)
type value = NumVal of num | BooleanVal of bool | StringVal of string | NilVal
   
type entry = Val of value | Fun of ident list * cmd

type state = ident -> entry option
let empty_state = fun x -> None
let lookup (s : state) (x : ident) : entry option = s x
let update (s : state) (x : ident) (e : entry) : state = fun y -> if y = x then Some e else s y


let rec eval_exp (e : exp) (s : state) : value option =
        match e with
        | Var x -> (match lookup s x with
                    | Some (Val v) -> Some v
                    | _ -> None)
        | Number n -> Some (NumVal n)      
        | Boolean b -> Some (BooleanVal b)
        | String s -> Some (StringVal s)
        | Table i -> None                       (*                                                              TODO            *)
        | Add (e1,e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (NumVal i1), Some (NumVal i2) -> (match (i1,i2) with
                                                                   | (Integer ii1, Integer ii2) -> Some (NumVal (Integer (ii1+ii2))) 
                                                                   | (Float f1, Float f2) -> None
                                                                   | (Integer ii1, Float f1) -> None
                                                                   | (Float f1, Integer ii1) -> None
                                                                   )
                          | _, _ -> None)
        | Mul (e1,e2) -> None
        | Sub (e1,e2) -> None
        | Div (e1,e2) -> None
        | Eq (e1,e2) -> None
        | And (e1,e2) -> None
        | Or (e1,e2) -> None



        

        let x = Some (NumVal (Float (0. + 1.1)))





        (*
        | Var x -> (match lookup s x with Some (Val v) -> Some v | _ -> None)
        | Num i -> Some (IntVal i)
        | Add (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                           | Some (IntVal i1), Some (IntVal i2) -> Some (IntVal (i1 + i2))
                           | _, _ -> None)
        | Sub (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                           | Some (IntVal i1), Some (IntVal i2) -> Some (IntVal (i1 - i2))
                           | _, _ -> None)
        | Bool b -> Some (BoolVal b)
        | And (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                           | Some (BoolVal b1), Some (BoolVal b2) -> Some (BoolVal (b1 && b2))
                           | _, _ -> None)
        | Or (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                           | Some (BoolVal b1), Some (BoolVal b2) -> Some (BoolVal (b1 || b2))
                           | _, _ -> None)
        | Eq (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                           | Some v1, Some v2 -> Some (BoolVal (v1 = v2))
                           | _, _ -> None)
      *)