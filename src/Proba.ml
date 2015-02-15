(** {1 Monads for probability distributions} *)

open Printf

(** {2 The signature of the monad for probability distributions} *)

type prob = float

type 'a distribution = ('a * prob) list

module type PROBA = sig

  type 'a mon

  val ret: 'a -> 'a mon
  val bind: 'a mon -> ('a -> 'b mon) -> 'b mon
  val (>>=): 'a mon -> ('a -> 'b mon) -> 'b mon

  val distr: 'a distribution -> 'a mon
    (** [distr d] chooses one value among zero, one or several,
        with the probabilities indicated in the distribution [d]. *)

  val flip: prob -> bool mon
    (** [flip p] returns the boolean [true] with probability [p]
        and [false] with probability [1-p]. *)

  val uniform: int -> int -> int mon
    (** [uniform lo hi] returns an integer between [lo] and [hi]
        included, with uniform probability. *)

  val choose: prob -> 'a mon -> 'a mon -> 'a mon
    (** [choose p a b] executes like [a] with probability [p]
        and like [b] with probability [1-p]. *)

  val fail: 'a mon
    (** Failure *)

  val observe: bool -> unit mon
    (* [observe b] continues (returning [()]) if [b] is [true]
       and fails if [b] is false. *)

  val run: int -> 'a mon -> 'a distribution * prob
    (* [run maxdepth m] explores the monadic computation [m]
       to maximal depth [m].  It returns a distribution of
       possible values, plus a combined probability for the
       parts of the monadic computation that were not explored
       because they exceed the maximal depth. *)


  val print_run: ('a -> unit) -> int -> 'a mon -> unit
    (* [print_run f maxdepth m] explores [m] like [run maxdepth m],
       then prints the resulting distribution using [f] to print
       individual values. *)
end

(** {2 Auxiliary functions for implementing monads} *)

(** Auxiliary for printing the results of a run *)

let print_run_aux (f: 'a -> unit) ((res, unknown): 'a distribution * prob) =
  List.iter
    (fun (x, p) -> printf "%10g: " p; f x; printf "\n")
    res;
  if unknown > 0.0 then
    printf "%10g: unknown\n" unknown

(** Auxiliary for removing duplicates from a distribution,
    accumulating their combined probabilities. *)

let remove_dups (l: 'a distribution) : 'a distribution =
  let rec remove l accu =
    match l with
    | [] -> accu
    | [xp] -> xp :: accu
    | (x1, p1 as xp1) :: ((x2, p2) :: l2 as l1) ->
        if x1 = x2
        then remove ((x1, p1 +. p2) :: l2) accu
        else remove l1 (xp1 :: accu)
  in List.rev (remove (List.sort (fun (x1,p1) (x2,p2) -> compare x1 x2) l) [])

(** Auxiliary to normalize the probabilities in a distribution
    so that they sum to 1. *)

let normalize ((res, unknown): 'a distribution * prob) =
  let total = 
    List.fold_left (fun tot (x, p) -> tot +. p) unknown res in
  (List.map (fun (x, p) -> (x, p /. total)) res, unknown /. total)

(** {2 The lazy probabilistic choice tree monad} *)

module Tree : PROBA = struct

  type 'a mon = unit -> 'a case distribution
  and 'a case = Val of 'a | Susp of 'a mon

  let ret (x: 'a) : 'a mon =
      fun () ->
          [ Val x, 1.0 ]

  let rec bind (m: 'a mon) (f: 'a -> 'b mon): 'b mon =
      fun () ->
          List.map
            (function
                | (Val a, p)   -> Susp (fun () -> f a ()), p
                | (Susp ma, p) -> Susp (fun () -> bind ma f ()), p)
            (m ())

  let (>>=) = bind

  let fail : 'a mon =
      fun () ->
          []

  let observe (b: bool) : unit mon =
    if b then ret () else fail

  let distr (d: 'a distribution) : 'a mon =
      fun () ->
          List.map (fun (a, p) -> Val a, p) d

  let flip (p: prob) : bool mon =
    distr [(true, p); (false, 1.0 -. p)]

  let rec range lo hi =
      if lo > hi 
      then []
      else lo :: range (lo + 1) hi

  let uniform (lo: int) (hi: int) : int mon =
      let n = float_of_int (hi - lo + 1) in
      fun () ->
          List.map (fun x -> Val x, 1. /. n) (range lo hi)

  let choose (p: prob) (a: 'a mon) (b: 'a mon) : 'a mon =
      fun () ->
          [ Susp a, p; Susp b, 1.0 -. p ]

  let prob_sum l =
      List.fold_left (fun p (_, p') -> p +. p') 0. l

  let normalize l =
      let prob = prob_sum l in
      List.map (fun (x, p) -> x, p /. prob) l

  let rec flatten (maxdepth: int) (m: 'a mon) : 'a case distribution =
      let flatten' maxdepth (v, p) =
          match v with
          | Val x  -> [ (Val x), p ]
          | Susp s ->
                  let f = flatten maxdepth s in
                  List.map (fun (c, p') -> c, p' *. p) f
      in
      if maxdepth <= 0
      then m ()
      else List.concat (List.map (flatten' (maxdepth - 1)) (m ()))


  let rec discriminate f l =
    match l with
    | [] -> ([], [])
    | elt::l' ->
        let (left, right) = discriminate f l' in
        match f elt with
        | `Left e -> (e :: left, right)
        | `Right e -> (left, e :: right)

  let run (maxdepth: int) (m: 'a mon) : 'a distribution * prob =
    let values, susps =
        flatten maxdepth m
        |> normalize
        |> discriminate (function (Val v, p) -> `Left (v, p) | (Susp m, p) -> `Right (m, p))
    in
    let keys = List.sort_uniq compare (List.map fst values) in
    let values =
        List.map (fun k -> k, prob_sum (List.filter (fun (k', p) -> k = k') values)) keys
    in
    let p_susp = prob_sum susps in
    values, p_susp

  let print_run f depth m = print_run_aux f (run depth m)

end
