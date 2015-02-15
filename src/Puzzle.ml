(** The bridge crossing puzzle *)

open Nondet.Naive   (* or:  open Nondet.Tree *)

type band_member = Bono | Edge | Adam | Larry

(** The actions that can be performed: *)
type action =
  | Forth of band_member * band_member  (** two persons walk forth on the bridge *)
  | Back of band_member                 (** one person walks back on the bridge *)

(** A trace of execution is the list of actions performed. *)
type trace = action list

(** This is the time it takes each person to cross the bridge. *)
let walking_time = function
  | Bono -> 1
  | Edge -> 2
  | Adam -> 5
  | Larry -> 10

(** A handy nondeterministic function: it takes a list and returns
  all the ways to decompose it into one element and the list of the
  other elements. *)

let rec take_one (l: 'a list) : ('a * 'a list) mon =
    match l with
    | []    -> fail
    | l::ls ->
        ret (l, ls)
        ||| (take_one ls >>= 
            function elt, lst -> ret (elt, l::lst))


(** Likewise, but decomposes the list in two distinct elements and
  the list of the other elements. *)

(* A naive implementation using take_one twice would generate duplicate
 * pairs (a, b, l) and (b, a, l). This is not the desired behaviour here *)
let rec take_two (l: 'a list) : ('a * 'a * 'a list) mon =
    match l with
    | [] | [_] -> fail
    | elt::l -> 
        (take_one l >>= function elt', l' ->
        ret (elt, elt', l'))
        ||| (take_two l >>= function elt1, elt2, l' ->
                ret (elt1, elt2, elt::l'))


(** The solution to the puzzle! *)
let solution: trace mon =
    let rec steps trace time back forth =

        take_two back >>= function (p1, p2, rest) ->
        let trace = Forth(p1, p2) :: trace in
        let time = time + max (walking_time p1) (walking_time p2) in
        let (forth, back) = (p1 :: p2 :: forth, rest) in

        if time > 17 then fail else
        if back = [] then ret trace else

        take_one forth >>= function (p1, rest) ->
        let trace = Back(p1) :: trace in
        (* this check is not necessary but prunes some dead branches early *)
        let time = time + walking_time p1 in
        if time > 17 then fail else 
        steps trace time (p1 :: back) rest
    in
    steps [] 0 [ Bono; Edge; Adam; Larry ] []

(** Printing the solution *)

open Printf

let name_of = function
  | Bono -> "Bono"
  | Edge -> "Edge"
  | Adam -> "Adam"
  | Larry -> "Larry"

let print_action = function
  | Forth(x, y) -> printf "%s and %s go forth" (name_of x) (name_of y)
  | Back(x) -> printf "%s goes back" (name_of x)

let print_trace t =
  List.iter (fun e -> print_action e; printf "; ") t

(* Using Nondet.Tree, 24 is the minimal depth for which the program is exhaustive *)
let _ =
  print_run print_trace 50 solution
