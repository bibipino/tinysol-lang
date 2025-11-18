(******************************************************************************)
(*                                    Tinysol CLI                             *)
(******************************************************************************)

open Ast
open Types
open Utils
open Main

let string_of_cli_cmd = function 
  | Faucet(a,n) -> "faucet " ^ a ^ " " ^ string_of_int n
  | Deploy(a,filename) -> "deploy " ^ a ^ " " ^ filename
  | ExecTx tx -> string_of_transaction tx
  | Assert(a,x,ev) -> "assert " ^ a ^ " " ^ x ^ " = " ^ string_of_exprval ev 

let is_assert = function 
  | Assert(_) -> true
  | _ -> false

let exec_cli_cmd (cc : cli_cmd) (st : sysstate) : sysstate = match cc with
  | Faucet(a,n) -> faucet a n st
  | Deploy(a,filename) -> 
      let c = filename |> read_file |> parse_contract 
      in st |> deploy_contract a c
  | ExecTx tx -> st |> exec_tx 1000 tx
  | Assert(a,x,ev) ->
      let v = 
        if x="balance" then Int(lookup_balance a st) 
        else lookup_var a x st
      in 
      if v = ev then st
      else failwith ("assertion violation: " ^ string_of_cli_cmd cc) 

let exec_cli_cmd_list (verbose : bool) (ccl : cli_cmd list) (st : sysstate) = 
  List.fold_left 
  (fun sti cc -> 
    if verbose && not (is_assert cc) then 
      print_endline (string_of_sysstate [] sti ^ "\n--- " ^ string_of_cli_cmd cc ^ " --->")
    else ();  
    try 
      exec_cli_cmd cc sti
    with ex -> print_endline (string_of_sysstate [] sti); raise ex)
  st
  ccl
