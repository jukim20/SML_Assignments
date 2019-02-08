(*
 * Jung U Kim
 * Sept. 28th, 2018
 *
 * CS 52, Fall 2018
 * Assignment 3
 *
 *)

(*** $-* ***)
(*
 * Common material: types and values for Mastermind
 *
 * See the assignment for discussion and details
 *
 *)
datatype peg = Red | Orange | Yellow | Green | Blue | Violet;

val allColors = [Red, Orange, Yellow, Green, Blue, Violet];

fun cons first rest = first::rest;
fun consAll lst elt = map (cons elt) lst;

fun possibilities elts k =
        if k < 0
           then []
        else if k = 0
           then [[]]
           else List.concat (map (consAll(possibilities elts (k-1))) elts);

val allCodes = possibilities allColors;

(* End of common material *)


(*** Problem 03_01   $- $+03_01 ***)
(* knuthShuffle : Random.rand -> 'a list -> 'a list *)

fun knuthShuffle gen lst =
    if length lst < 2
       then lst
       else
	   let 
	       val random = Random.randRange(0, length lst - 1) gen;
	       val randElt = List.nth (lst, random);
	       val rest = List.filter (fn x => x <> randElt) lst;
	   in
	       randElt :: (knuthShuffle gen (rest))
	   end;




(*** Problem 03_02   $-03_01 $+03_02 ***)
(* exactMatches : ''a list -> ''a list -> int *)

fun exactMatches []      _       = 0
  | exactMatches _       []      = 0
  | exactMatches (x::xs) (y::ys) = if x = y
				      then 1 + exactMatches xs ys
				      else exactMatches xs ys;




(*** Problem 03_03a   $-03_02 $+03_03a ***)
(* countColors : peg list -> int list *)

fun countColors []      = []
  | countColors (x::xs) =
    let
	fun countColorsAux []      color = 0
	  | countColorsAux (x::xs) color = if x = color
					      then 1 + (countColorsAux xs color)
					      else countColorsAux xs color;

	val countRed = countColorsAux (x::xs) Red;
	val countOrange = countColorsAux (x::xs) Orange;
	val countYellow = countColorsAux (x::xs) Yellow;
	val countGreen = countColorsAux (x::xs) Green;
	val countBlue = countColorsAux (x::xs) Blue;
	val countViolet = countColorsAux (x::xs) Violet;
    in
	countRed::countOrange::countYellow::countGreen::countBlue::countViolet::[]
    end;





(*** Problem 03_03b   $-03_03a $+03_03b ***)
(* totalMatches : peg list -> peg list -> int *)

fun totalMatches []   _     = 0
  | totalMatches _    []    = 0
  | totalMatches code guess =
    let
	fun sumAll []      = 0
	  | sumAll (x::xs) = x + sumAll xs;

	val countCode = countColors code;
	val countGuess = countColors guess;

	fun totalMatchesAux []      _       = []
	  | totalMatchesAux _       []      = []
	  | totalMatchesAux (x::xs) (y::ys) =
	    if x < y
	    then x :: (totalMatchesAux xs ys)
	    else y :: (totalMatchesAux xs ys);

    in
	sumAll (totalMatchesAux countCode countGuess)
    end;






(*** Problem 03_04   $-03_03b $+03_04 ***)
(* matches : peg list -> peg list -> int * int *)

fun matches code guess = ((exactMatches code guess),
                          (totalMatches code guess) - (exactMatches code guess));







(*** Problem 03_05   $-03_04 $+03_05 ***)
(* isConsistent : peg list -> int * int -> peg list -> bool *)

fun isConsistent guess (x,y) candidate = ((x,y) = (matches candidate guess));






(*** Problem 03_06   $-03_05 $+03_06 ***)
(* filterCodes : peg list -> int * int -> 
 *                   peg list list -> peg list list
 *)

fun filterCodes _     (_,_) []                  = []
  | filterCodes []    (_,_) _                   = []
  | filterCodes guess (x,y) (candidateList::cs) =
    if isConsistent guess (x,y) candidateList
       then candidateList :: filterCodes guess (x,y) cs
       else filterCodes guess (x,y) cs;





(*** Problem 03_07a   $-03_06 $+03_07a ***)
(* codebreaker : (peg list -> int * int) -> peg list list -> 
 *              peg list list -> peg list list
 *)

exception InternalInconsistency;

fun codebreaker f guessLst []              = raise InternalInconsistency
  | codebreaker f guessLst (candidate::cs) =
    if f candidate = (length candidate, 0)
    then rev (candidate::guessLst)
    else codebreaker f (candidate::guessLst) (filterCodes candidate (f candidate) cs);




(*** Problem 03_07b   $-03_07a $+03_07b ***)
(* solve : peg list -> peg list list *)

fun solve secretCode = codebreaker (matches secretCode) ([])
				   (allCodes (List.length secretCode));





(*** Problem 03_08   $-03_07b $+03_08 ***)
(* digitToChar : int -> char *)

exception RadixException;

fun digitToChar n =
    if n < 0 orelse n > 20
       then raise RadixException
       else 
           let
               val numList = [#"0", #"1", #"2", #"3", #"4", #"5", #"6", #"7", #"8", #"9"];
               val charList = [#"A", #"B", #"C", #"D", #"E", #"F", #"G", #"H", #"J", #"K", #"L"];
           in
               if n <= 9
                  then List.nth (numList, n)
                  else List.nth (charList, n-10)
           end;




(*** Problem 03_09   $-03_08 $+03_09 ***)
(* charToDigit : char -> int *)

fun charToDigit c =
    if (ord c) < 48 orelse (ord c) = 73 orelse (ord c) > 76
       then raise RadixException
    else if (ord c) > 73 andalso (ord c) <= 76
       then (ord c) - 56
    else if (ord c) >= 65 andalso (ord c) < 73
       then (ord c) - 55
       else (ord c) - 48;





(*** Problem 03_10   $-03_09 $+03_10 ***)
(* fromRadixString : int * string -> int *)

fun fromRadixString (_, "") = 0
  | fromRadixString (0, _) = 0                                            
  | fromRadixString (radix, string) =
    if radix <2 orelse radix > 20
       then raise RadixException
       else
           let
               fun power (n, k) =
                   if k < 0
                      then 0
                   else if k = 0
                      then 1
                      else n * (power (n, k-1));

               val charList = explode string
               val digitList = map charToDigit (charList)
               val powered = power (radix, (length digitList - 1))             
               val checkNextDigit = implode (List.drop (charList, 1))
           in
               (List.nth (digitList, 0) * powered)
	       +
	       (fromRadixString (radix, checkNextDigit))
           end;




(*** Problem 03_11   $-03_10 $+03_11 ***)
(* toRadixString : int * int -> string *)

fun toRadixString (radix, i) =
    if radix < 2 orelse radix > 20
       then raise RadixException
       else
           let
               fun toRadixStringAux acc (_,0) = acc
                 | toRadixStringAux acc (radix, i) = toRadixStringAux ((i mod radix)::acc)
								      (radix, (i div radix));

               val result = toRadixStringAux nil (radix, i)
               val charResult = map digitToChar (result)
 
           in
               implode charResult
           end;





(*** $-03_11 ***)
