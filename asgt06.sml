(*
 * Jung U Kim
 * Nov. 9th, 2018
 *
 * CS 52, Fall 2018
 * Assignment 6
 *
 *)

(*** Starter code   $-* $+ ***)
(*
 * Starter code, part 1 of 3, data types
 *
 * oper: the arithmetic operations
 *
 * token: the results of a lexical scan
 *
 * syntaxTree: the result of a parse operation
 *)
datatype oper =
    Negate
  | Plus
  | Minus
  | Times
  | Divide
  | Remainder;

datatype token = 
    Number of int
  | Operation of oper
  | LParen
  | RParen
  | Semicolon;

datatype syntaxTree =
    Uninode of oper * syntaxTree
  | Binode of syntaxTree * oper * syntaxTree
  | Leaf of int;

(*
 * Starter code, part 2 of 3, exceptions
 *
 * When one of your functions encounters an error, it should raise an
 * exception with a descriptive message. In a top-level function, you 
 * will introduce code to handle the exceptions that are raised; see 
 * Problem~4.
 *)
exception LexicalException of string;
exception GrammarException of string;
exception CodeException of string;

(*
 * Starter code, part 3 of 3, an error-reporting utility
 *
 * These functions are for writing values out of the SML system. They are
 * executed not for the values they return, but for their side effects, and
 * so they violate the functional paradigm. We shall simply use them when 
 * necessary and not worry too much about the implementation.
 *
 * errorln: print an error message on the standard error stream, on a line
 * by itself. It returns nil because it is intended to be used with the 
 * function compile in Problem 4, which returns a list of strings.
 *)
val exitCode = ref OS.Process.success;
fun errorln str = (exitCode := OS.Process.failure;
                   TextIO.output (TextIO.stdErr, str ^ "\n");
                   TextIO.flushOut TextIO.stdErr;
                   nil);

(*** Problem 1   $- $+06_01 ***)
(* scan : char list -> token list *)

fun scan []           = []
  | scan (#"~" :: xs) = Operation Negate :: scan xs
  | scan (#"+" :: xs) = Operation Plus :: scan xs
  | scan (#"-" :: xs) = Operation Minus :: scan xs
  | scan (#"*" :: xs) = Operation Times :: scan xs
  | scan (#"/" :: xs) = Operation Divide :: scan xs
  | scan (#"%" :: xs) = Operation Remainder :: scan xs
  | scan (#")" :: xs) = RParen :: scan xs
  | scan (#"(" :: xs) = LParen :: scan xs
  | scan (#";" :: xs) = Semicolon :: scan xs
  | scan (#" " :: xs) = scan xs
  | scan (x    :: xs) = if Char.isDigit x
			then scanAux 0 (x::xs)
			     handle Overflow => raise LexicalException "integer too large"
			else raise LexicalException "illegal character"

and scanAux acc []      = Number acc :: []
  | scanAux acc (x::xs) = if Char.isDigit x
			  then scanAux (acc * 10 + (ord x - ord #"0")) xs
			  else Number acc :: scan (x::xs);
								   
			       
(*** Problem 2   $-06_01 $+06_02 ***)
(* parse : token list -> syntax tree *)

fun expn tknList = coExpn (term tknList)
and coExpn (tr, (Operation Plus :: rest)) =
    let
        val (rtree, rrest) = term rest;
    in
        coExpn (Binode (tr, Plus, rtree), rrest)
    end
  | coExpn (tr, (Operation Minus :: rest)) =
    let
        val (rtree, rrest) = term rest;
    in
        coExpn (Binode (tr, Minus, rtree), rrest)
    end
  | coExpn (tr, rest)                      = (tr, rest)
                    
and term tknList = coTerm (factor tknList)
and coTerm (tr, (Operation Times) :: rest)     =
    let
	val (rtree, rrest) = factor rest;
    in
	coTerm (Binode (tr, Times, rtree), rrest)
    end
  | coTerm (tr, (Operation Divide) :: rest)    =
    let
	val (rtree, rrest) = factor rest;
    in
	coTerm (Binode (tr, Divide, rtree), rrest)
    end
  | coTerm (tr, (Operation Remainder) :: rest) =
    let
	val (rtree, rrest) = factor rest;
    in
	coTerm (Binode (tr, Remainder, rtree), rrest)
    end
  | coTerm (tr, rest)                          = (tr, rest)

and factor (Operation Negate :: rest) =
    let
        val (rtree, rrest) = posfactor rest;
    in
        (Uninode (Negate, rtree), rrest)
    end
  | factor tknList = posfactor tknList

and posfactor (LParen :: rest) =
    let
        val (rtree, rrest) = expn rest;
        val (x :: xs) = rrest;
    in
        if x = RParen
        then (rtree, xs)
        else raise GrammarException "right parenthesis expected"
    end
  | posfactor tknList = number tknList
                                    
and number (Number n :: rest) = (Leaf n, rest)
  | number _ = raise GrammarException "number expected";

fun parse tknList =
    let
        val (rtree, rrest) = expn tknList;
        val (x :: xs) = if rrest = []
                        then raise GrammarException "semicolon expected"
                        else rrest;
        
    in
        if x = Semicolon andalso xs = []
        then rtree
        else raise GrammarException "extra tokens"
    end;




(*** Problem 3   $-06_02 $+06_03 ***)
(* encode : syntax tree -> string list *)

fun encodeAux (Leaf k) = [" lcw r3 " ^ Int.toString k,
                         " psh r3"]
  | encodeAux (Uninode (Negate, stree))     = encodeAux stree
                                              @
                                              [" pop r3",
                                               " neg r3 r3",
                                               " psh r3"]

  | encodeAux (Binode (ltree, Plus, rtree)) = encodeAux ltree @ encodeAux rtree
                                              @
                                              [" pop r2",
                                              " pop r3",
                                              " add r3 r3 r2",
                                              " psh r3"]
  | encodeAux (Binode (ltree, Minus, rtree)) = encodeAux ltree @ encodeAux rtree
                                               @
                                               [" pop r3",
                                               " pop r2",
                                               " sub r3 r2 r3",
                                               " psh r3"]
  | encodeAux (Binode (ltree, Times, rtree)) = encodeAux ltree @ encodeAux rtree
                                                @
                                                [" pop r3",
                                                " lcw r2 mlmul",
                                                " cal r2 r2",
                                                " pop r0",
                                                " psh r3"]
  | encodeAux (Binode (ltree, Divide, rtree)) = encodeAux ltree @ encodeAux rtree
                                                 @
                                                 [" pop r3",
                                                 " lcw r2 dldiv",
                                                 " cal r2 r2",
                                                 " pop r0",
                                                 " psh r3"]
  | encodeAux (Binode (ltree, Remainder, rtree)) = encodeAux ltree @ encodeAux rtree
                                                   @
                                                   [" pop r3",
                                                    " lcw r2 dldiv",
                                                    " cal r2 r2"]
  | encodeAux _                               = raise CodeException "invalid syntax tree"

fun encode stree = ["BEGIN",
                    " lcw r1 stack"]
                    @ (encodeAux stree)
                    @ [" pop r3",
                    " sto r3 r0",
                    " hlt",
                    " inc mullib",
                    " inc divilib",
                    " dat 100",
                    "stack",
                    "END"]

(*** Problem 4   $-06_03 $+06_04 ***)
(* compile : string -> string list *)

fun compile str = (encode o parse o scan o explode) str
                  handle LexicalException msg => errorln ("Lexical error: " ^ msg)
                       | GrammarException msg => errorln ("Grammar error: " ^ msg)
                       | CodeException msg => errorln ("Code error: " ^ msg)
                                      


(*** Problem 5   $-06_04 ***)
(*
 * There is no code to write for Problem 5. Simply
 * invoke the driver file as described in the a  ssignment.
 *)
