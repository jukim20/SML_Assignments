(*
 * Jung U Kim
 * Sept. 21st, 2018
 *
 * CS 52, Fall 2018
 * Assignment 2
 *
 *)

(*** $-* ***)

(*** Problem 02_01a   $- $+02_01a ***)
(* precart : 'a -> 'b list -> ('a * 'b) list *)

fun precart _ []      = []
  | precart n (x::xs) = (n, x) :: precart n xs; 





(*** Problem 02_01b   $-02_01a $+02_01b ***)
(* cartesian : 'a list -> 'b list -> ('a * 'b) list *)

fun cartesian _       []    = []
  | cartesian []      _     = []
  | cartesian (x::xs) yList = (precart x yList) @ (cartesian xs yList); 





(*** Problem 02_02a   $-02_01b $+02_02a ***)
(* fromDigitList : int list -> int *)

exception BadDigit
	      
fun fromDigitList []      = 0
  | fromDigitList (x::xs) = if x < 0 orelse x > 9
			       then raise BadDigit
			       else x + 10 * (fromDigitList xs);




(*** Problem 02_02b   $-02_02a $+02_02b ***)
(* toDigitList : int -> int list *)

exception NegativeNumber;

fun toDigitList 0 = []
  | toDigitList x = if x < 0
		       then raise NegativeNumber
		       else (x mod 10) :: toDigitList (x div 10);





(*** Problem 02_03a   $-02_02b $+02_03a ***)
(* stringToIntList : string -> int list *)

exception NotADigit;

fun digitToInt c = if Char.isDigit c
		      then ord c - ord #"0"
		      else raise NotADigit;

fun intToDigit k = if 0 <= k andalso k < 10
		      then chr (k + ord #"0")
		      else raise NotADigit;

fun stringToIntList str = rev (map digitToInt (explode str))





(*** Problem 02_03b   $-02_03a $+02_03b ***)
(* doubleDigitSum : int -> int *)

fun doubleDigitSum k = if k >= 0 andalso k < 5
		          then 2*k
		          else 2*k - 9;





(*** Problem 02_04   $-02_03b $+02_04 ***)
(* luhnSum : int list -> int *)

fun luhnSum []         = 0
  | luhnSum [x]        = x
  | luhnSum (x::y::xs) = x + doubleDigitSum y + luhnSum xs;





(*** Problem 02_05a   $-02_04 $+02_05a ***)
(* luhnCheck : string -> bool *)

fun luhnCheck str = luhnSum (stringToIntList str) mod 10 = 0;





(*** Problem 02_05b   $-02_05a $+02_05b ***)
(* calculateCheckDigit : string -> int *)

fun calculateCheckDigit str = luhnSum ([0] @ (stringToIntList str)) mod 10;




(*** Problem 02_05c   $-02_05b $+02_05c ***)
(* accountNumber *)

(* Account number remains valid when the adjacent digits that are switched are 9 and 0.
 * Therefore, an example of this would be 274390. *) 




(*** Problem 02_06   $-02_05c $+02_06 ***)
(* change : int list -> int -> int list list *)

fun consAll []      _ = []
  | consAll (x::xs) k = (k::x) :: (consAll xs k); 

fun change []      _ = []
  | change (x::xs) n = if n < 0
		          then []
		       else if n = 0
		          then [[]]
		          else (consAll (change (x::xs) (n-x)) x) @ (change xs n);




(*** Problem 02_07a   $-02_06 $+02_07a ***)
(* keepFirst : ''a list -> ''a list *)

fun keepFirst []      = []
  | keepFirst (x::xs) =
    let
	fun member u []      = false
	  | member u (x::xs) = x=u orelse (member u xs);
		  
        fun keepFirstAux acc []      = acc
	  | keepFirstAux acc (x::xs) = if member x acc
		    	     	          then keepFirstAux acc xs
				          else keepFirstAux (acc@[x]) xs;
    in
	keepFirstAux nil (x::xs)
    end;



(*** Problem 02_07b   $-02_07a $+02_07b ***)
(* subst : string -> (char * char) list *)

fun subst s =
    let
	val alphabets = explode "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
	val message = keepFirst (explode s);
    in
	ListPair.zip (alphabets, message)
    end;




(*** Problem 02_08a   $-02_07b $+02_08a ***)
(* substEncipher : string * string -> string *)

fun substEncipher (pangram, plainString) =
    let
	fun funPairs default []           _ = default
          | funPairs default ((u,v)::uvs) x =
            if u = x
               then v
               else funPairs default uvs x;

	fun sanitize []      = []
	  | sanitize (x::xs) =
	    if (Char.isAlpha x andalso Char.isUpper x) orelse Char.isSpace x
	       then x :: (sanitize xs)
	    else if Char.isAlpha x
	       then (Char.toUpper x) :: (sanitize xs)
	       else sanitize xs;
	
	val key = subst pangram
	val plainList = sanitize (explode plainString)	
	val encrypt = funPairs #"," key
	val cipherList = map encrypt plainList;
    in
	implode cipherList
    end;






(*** Problem 02_08b   $-02_08a $+02_08b ***)
(* substDecipher : string * string -> string *)

fun substDecipher (pangram, cipherString) =
    let
	fun funPairs default [] _           = default
          | funPairs default ((u,v)::uvs) x =
            if u = x
            then v
            else funPairs default uvs x;
	    
	val key = subst pangram
	
	val cipherList = explode cipherString

	fun reverse []          = []
	  | reverse ((x,y)::xs) = ((y,x):: reverse xs);
	
	val decryptKey = reverse key
	val decrypt = funPairs #"," decryptKey
	val decipherList = map decrypt cipherList;
    in
	implode decipherList
    end;




(*** $-02_08b ***)
