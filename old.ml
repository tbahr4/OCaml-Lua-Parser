
(* Identifiers are of type string *)
type ident = string
type num = Integer of int | Float of float

(* Datatypes *)
type typ = BooleanType | NumberType | StringType | TableType



(* Expressions *)
type exp = Number of num    (* Numbers may be float or int *)
        | Boolean of bool 
        | String of string
        | Table of ident    (* x *)
        | Add of exp * exp  (* a + b *) 
        | Mul of exp * exp  (* a * b *)
        | Sub of exp * exp  (* a - b *)
        | Div of exp * exp  (* a / b *)
        | Var of ident      (* x *)
        | Eq of exp * exp   (* a = b *)
        | And of exp * exp  (* a and b *)






(* typecheck *)
(* Returns true if exp e is of type t *)
let rec typecheck (e : exp) (t : typ) : bool = 
    match e with
    | Number _ -> t = NumberType (* Return true if number is of type NumberType *)
    | Boolean _ -> t = BooleanType 
    | String _ -> t = StringType
    | Table _ -> t = TableType
    | Add (e1,e2) -> (typecheck e1 NumberType) && (typecheck e2 NumberType) && (t = NumberType) (* Return true if e1 and e2 are numbers and t is number *)
    | Mul (e1,e2) -> (typecheck e1 NumberType) && (typecheck e2 NumberType) && (t = NumberType)
    | Sub (e1,e2) -> (typecheck e1 NumberType) && (typecheck e2 NumberType) && (t = NumberType)
    | Div (e1,e2) -> (typecheck e1 NumberType) && (typecheck e2 NumberType) && (t = NumberType)
    | Var e1 -> false     (* impl later with lookup *)
    | Eq (e1,e2) -> ((typecheck e1 BooleanType && typecheck e2 BooleanType) || (typecheck e1 NumberType && typecheck e2 NumberType) || (typecheck e1 StringType && typecheck e2 StringType)) && t = BooleanType
    | And (e1,e2) -> (typecheck e1 BooleanType) && (typecheck e2 BooleanType) && (t = BooleanType)      (* Lua allows comparing 'and' with strings and ints, but not necessary to implement *)
;;

(* Tests *)

(* Number *)
let number1 = typecheck (Number(Integer 3)) (NumberType);;
let number2 = typecheck (Number(Float 3.34)) (NumberType);;
(* Boolean *)
let boolean1 = typecheck (Boolean true) (BooleanType);;
let boolean2 = typecheck (Boolean false) (BooleanType);;
(* String *)
let string1 = typecheck (String "s") (StringType);;
(* Table *)
let table1 = typecheck (Table "tableIdent") (TableType);;
(* Add *)
let add1 = typecheck (Add(Number(Integer 3), Number(Float 3.34))) (NumberType);;
(* Mul *)
let mul1 = typecheck (Mul(Number(Integer 3), Number(Float 3.34))) (NumberType);;
(* Sub *)
let sub1 = typecheck (Sub(Number(Integer 3), Number(Float 3.34))) (NumberType);;
(* Div *)
let div1 = typecheck (Div(Number(Integer 3), Number(Float 3.34))) (NumberType);;
(* Var *)
let var1 = typecheck (Var("x")) (BooleanType)
let var2 = typecheck (Var("y")) (StringType)
let var3 = typecheck (Var("z")) (NumberType)
(* Eq *)
let eq1 = typecheck (Eq(Number(Integer 3), Number(Float 3.34))) (BooleanType);;
let eq2 = typecheck (Eq(Boolean true, Boolean false)) (BooleanType);;
let eq3 = typecheck (Eq(String "s", String "s2")) (BooleanType);;
(* And *)
let and1 = typecheck (And(Boolean true, Boolean false)) (BooleanType);;