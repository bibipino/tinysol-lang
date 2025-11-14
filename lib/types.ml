open Ast

(* exprval: values associated to (contract and local) variables *)

type exprval = Bool of bool | Int of int | Addr of string

(* TODO: not used yet *)
type envval  = IVar of exprval | IProc of args * cmd

(* local environment: 
    maps local variables, plus sender and value
    this is a transient storage, not preserved between calls
*)
type env = ide -> exprval

(* contract state: persistent contract storage, preserved between calls *)
type contract_state = {
  balance : int;
  storage : ide -> exprval;
}

type sysstate = {
  users: addr -> int;                 (* EOA state = ETH balance *)
  contracts: addr -> contract_state;  (* Contract state = ETH balance * storage *)
  stackenv: env list;
}

(* execution state *)
type exec_state = 
  | St of sysstate 
  | Cmd of cmd * sysstate * addr

(* the state of an address depends on the type of address:
    EOA:      amount of ETH held by the address
    Contract: amount of ETH plus mapping from state variables to values
 *)
type addrinfo = 
  | EOA 
  | Contr of contract

(* global environment *)
type genv = addr -> addrinfo 


(* Functions to access and manipulate the state *)

let topenv (st: sysstate) : env = match st.stackenv with
  [] -> failwith "empty stack"
| e::_ -> e

let popenv (st: sysstate) : env list = match st.stackenv with
    [] -> failwith "empty stack"
  | _::el -> el

let botenv = fun x -> failwith ("variable " ^ x ^ " unbound")
let botstorage = fun a -> failwith ("address " ^ a ^ " unbound")
    
let bind f x v = fun y -> if y=x then v else f y

(* lookup for variable x in state st (tries first in storage of address a) *)
    
let lookup (st : sysstate) (a : addr) (x : ide) : exprval =
  try 
    (* look up for x in environment *)
    let e = topenv st in
    e x
  with _ -> 
    (* look up for x in storage of a *)
    let cs = st.contracts a in
    cs.storage x

let mem_contract_state (cs : contract_state) (x : ide) : bool = 
  try let _ = cs.storage x in true
  with _ -> false

let mem_env (r:env) (x:ide) : bool =
  try let _= r x in true
  with _ -> false

let update_storage (st : sysstate) (a:addr) (x:ide) (v:exprval) : sysstate = 
  let cs = st.contracts a in
    if mem_contract_state cs x then 
      let cs' = { cs with storage = bind cs.storage x v } in 
      { st with contracts = bind st.contracts a cs' }
    else failwith (x ^ " not bound in storage of " ^ a)   

let update_env (st : sysstate) (x:ide) (v:exprval) : sysstate =
  let el = st.stackenv in match el with
  | [] -> failwith "Empty stack"
  | e::el' -> 
    if mem_env e x then 
      let e' = bind e x v in 
      { st with stackenv = e'::el' }
    else failwith (x ^ " not bound in env")   

exception TypeError of string
exception UnboundVar of ide
