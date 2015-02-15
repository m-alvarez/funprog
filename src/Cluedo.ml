(* A game of Bayesian Cluedo *)

open Printf
open Proba.Tree

type suspect = Alice | Bob

type weapon = Gun | Pipe

let whodunnit : suspect mon =
  choose 0.3 (ret Alice) (ret Bob) >>= fun suspect ->
    (match suspect with
    | Alice -> choose 0.97 (ret Pipe) (ret Gun)
    | Bob -> choose 0.8 (ret Gun) (ret Pipe))
    >>= function
    | Gun -> fail
    | Pipe -> ret suspect

let print_suspect = function
  | Alice -> printf "Alice"
  | Bob   -> printf "Bob"

(* the classical solution *)
let rec prob a =
  match a with
  | `Alice -> 0.3
  | `Bob -> 0.7
  | `Gun | `Pipe -> 
      prob `Alice *. prob_given a `Alice
        +. prob `Bob *. prob_given a `Bob
and prob_given a b =
  match (a, b) with
  | (`Gun, `Alice) -> 0.03
  | (`Pipe, `Alice) -> 0.97
  | (`Gun, `Bob) -> 0.8
  | (`Pipe, `Bob) -> 0.2
  | (`Bob, `Bob) | (`Alice, `Alice) -> 1.0
  | (`Alice, `Bob) | (`Bob, `Alice) -> 0.0
  | (a, b) ->
      prob a *. prob_given b a /. prob b

let _ =
  printf "The result using monadic programming is:\n";
  print_run print_suspect 20 whodunnit;
  printf "The result using Bayes' theorem is:\n";
  printf "  %f: Alice\n" (prob_given `Alice `Pipe);
  printf "  %f: Bob\n" (prob_given `Bob `Pipe)



