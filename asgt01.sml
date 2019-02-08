(*
 * Jung U Kim
 * Sept. 10th, 2018
 *
 * CS 52, Fall 2018
 * Assignment 1
 *
 *)

(*** $-* ***)
(*** Problem 1   $- $+01_01 $+01_05 ***)
(* cube : int -> int *)

fun cube n = n *  n * n;


(*** Problem 2   $-01_01 $-01_05 $+01_02 ***)
(* min3 : int * int * int -> int *)

fun min3 (x, y, z) = if x <= y andalso x <= z
		        then x
		     else if y <= x andalso y <= z
		        then y
		        else z;


(*** Problem 3a   $-01_02 $+01_03a ***)
(* factorial : int -> int *)

fun factorial n = if n < 0
		     then 0
		  else if n = 0
		     then 1
		     else n * factorial (n-1);


(*** Problem 3b   $-01_03a $+01_03b ***)
(* maxFactorial : int *)

val maxFactorial = 12;


(*** Problem 3c   $-01_03b $+01_03c ***)
(* realFactorial : int -> real *)

fun realFactorial n = if n < 0
		         then 0.0
		      else if n = 0
		         then 1.0
		         else real (n) * realFactorial (n-1);



(*** Problem 3d   $-01_03c $+01_03d ***)
(* maxRealFactorial : int *)

val maxRealFactorial = 170;


(*** Problem 4   $-01_03d $+01_04 ***)
(* myLength : 'a list -> int *)

fun myLength []      = 0
  | myLength (x::xs) = 1 + myLength xs;

(*** Problem 5   $-01_04 $+01_05 ***)
(* cubeAll : int list -> int list *)

fun cubeAll []      = []
  | cubeAll (x::xs) = (cube x) :: (cubeAll xs);


(*** Problem 6   $-01_05 $+01_06 ***)
(* duplicate : 'a list -> 'a list *)

fun duplicate []      = []
  | duplicate (x::xs) = (x :: (x :: duplicate xs));


(*** Problem 7   $-01_06 $+01_07 ***)
(* lessThanList : int -> int list -> bool *)

fun lessThanList _ []      = true
  | lessThanList n (x::xs) = if n < x
			        then lessThanList n xs
			        else false;
				      


(*** Problem 8   $-01_07 $+01_08 ***)
(* myAppend : 'a list -> 'a list -> 'a list *)

fun myAppend []      []      = []
  | myAppend (x::xs) []      = (x::xs)
  | myAppend []      (y::ys) = (y::ys)
  | myAppend (x::xs) (y::ys) = x :: (myAppend xs (y::ys));


(*** Problem 9   $-01_08 $+01_09 ***)
(* myFilter : ('a -> bool) -> 'a list -> 'a list *)

fun myFilter f []      = []
  | myFilter f (x::xs) = if f x
			    then x :: myFilter f xs
			    else myFilter f xs;

(*** Problem 10   $-01_09 $+01_10 ***)
(* myZip : 'a list * 'b list -> ('a * 'b) list *)

fun myZip ([]     , _)       = []
  | myZip (_      , [])      = []
  | myZip ((x::xs), (y::ys)) = (x, y) :: myZip (xs, ys);


(*** Problem 11   $-01_10 $+01_11 $+01_14 ***)
(* cycle: int -> 'a list -> 'a list *)

fun cycleAux []      = []
  | cycleAux (x::xs) = xs @ [x];

fun cycle _ []  = []
  | cycle 0 lst = lst
  | cycle n lst = if n < 0
		     then cycle (length lst + n) lst
		     else cycle (n-1) (cycleAux lst);


(*** Problem 12   $-01_14 $-01_11 $+01_12 ***)
(* consAll : 'a list list -> 'a -> 'a list list *)

fun consAll []      _ = []
  | consAll (x::xs) n = (n::x) :: (consAll xs n);


(*** Problem 13   $-01_12 $+01_13 $+01_14 ***)
(* sanitize : char list -> char list *)

fun sanitize []      = []
  | sanitize (x::xs) = if (Char.isAlpha x andalso Char.isUpper x) orelse Char.isSpace x
		          then x :: (sanitize xs)
		       else if Char.isAlpha x
		          then (Char.toUpper x) :: (sanitize xs)
		          else sanitize xs;


(*** Problem 14   $-01_14 $-01_13 $+01_14 ***)
(* caesar : int * string -> string *)

fun caesar (n, plainString) =
    let
	fun funPairs default nil          _ = default
	  | funPairs default ((u,v)::uvs) x =
               if u = x
                  then v
               else funPairs default uvs x;

	val plainList  = sanitize (explode plainString);
	
	val alphabets  = "ABCDEFGHIJKLMNOPQRSTUVWXYZ ";
	val alphaList = explode alphabets;
	val cycledAlpha = cycle n alphaList;
	val pairAlpha = ListPair.zip (alphaList, cycledAlpha);
	val encode = funPairs #"," pairAlpha;

	val cipherList = map encode plainList; 
    in
	implode cipherList
    end;


(*** $-01_14 ***)
