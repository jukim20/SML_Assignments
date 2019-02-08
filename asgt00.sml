(*
 * Jung U (Ellen) Kim
 * Sept. 4th, 2018
 *
 * CS 52, Fall 2018
 * Assignment 0
 *
 *)
(*** $-* ***)

(*** Problem 1   $+00_01 ***)
(* numList : int -> int list *)

fun numList n = if 0 < n
		   then n::(numList (n-1))
		   else nil;


(*** Problem 2   $-00_01 $+00_02 ***)
(* sumList : int -> int *)

fun sumList n = if 0 < n
		   then n + sumList (n-1)
		   else 0;


(*** Problem 3   $-00_02 $+00_03 ***)
(* sumFormula : int -> int *)

fun sumFormula n = n * (n+1) div 2;


(*** Problem 4   $-00_03 $+00_04 ***)
(* sameValues : 'a list -> 'a list -> bool *)

fun sameValues nil      nil 	   = true
  | sameValues (x::xs)  (y::ys)    = x=y andalso sameValues xs ys
  | sameValues _        _          = false;


(*** Problem 5   $-00_04 $+00_05 ***)
(* Verification that the two computations give equal values *)

val baseList = numList 47;
val siValues = map sumList baseList;
val sfValues = map sumFormula baseList;
sameValues siValues sfValues;


(*** $-00_05 ***)
