(* CMSC 330 / Spring 2015 / Project 4 *)
(* Name: Harry Young *)
(* Login: Hyoung12 *)

#load "str.cma"

(* ------------------------------------------------- *)
(* MODULE SIGNATURE *)
(* ------------------------------------------------- *)

module type NFA =
  sig
    (* You may NOT change this signature *)

    (* ------------------------------------------------- *)
    (* PART 1: NFA IMPLEMENTATION *)
    (* ------------------------------------------------- *)

    (* ------------------------------------------------- *)
    (* Abstract type for NFAs *)
    type nfa

    (* Type of an NFA transition.

       (s0, Some c, s1) represents a transition from state s0 to state s1
       on character c

       (s0, None, s1) represents an epsilon transition from s0 to s1
     *)
    type transition = int * char option * int 

    (* ------------------------------------------------- *)
    (* Returns a new NFA.  make_nfa s fs ts returns an NFA with start
       state s, final states fs, and transitions ts.
     *)
    val make_nfa : int -> int list -> transition list -> nfa

    (* ------------------------------------------------- *)
    (*  Calculates epsilon closure in an NFA.  

	e_closure m ss returns a list of states that m could 
	be in, starting from any state in ss and making 0 or 
	more epsilon transitions.

       There should be no duplicates in the output list of states.
     *)

    val e_closure : nfa -> int list -> int list

    (* ------------------------------------------------- *)
    (*  Calculates move in an NFA.  

	move m ss c returns a list of states that m could 
	be in, starting from any state in ss and making 1
	transition on c.

       There should be no duplicates in the output list of states.
     *)

    val move : nfa -> int list -> char -> int list

    (* ------------------------------------------------- *)
    (* Returns true if the NFA accepts the string, and false otherwise *)
    val accept : nfa -> string -> bool

    (* ------------------------------------------------- *)
    (* PART 2: REGULAR EXPRESSION IMPLEMENTATION *)
    (* ------------------------------------------------- *)

    (* ------------------------------------------------- *)
    type regexp =
	Empty_String
      | Char of char
      | Union of regexp * regexp
      | Concat of regexp * regexp
      | Star of regexp

    (* ------------------------------------------------- *)
    (* Given a regular expression, print it as a regular expression in 
       postfix notation (as in project 2).  Always print the first regexp 
       operand first, so output string will always be same for each regexp.
     *)
    val regexp_to_string : regexp -> string 

    (* ------------------------------------------------- *)
    (* Given a regular expression, return an nfa that accepts the same
       language as the regexp
     *)
    val regexp_to_nfa : regexp -> nfa

    (* ------------------------------------------------- *)
    (* PART 3: REGULAR EXPRESSION PARSER *)
    (* ------------------------------------------------- *)

    (* ------------------------------------------------- *)
    (* Given a regular expression as string, parses it and returns the
       equivalent regular expression represented as the type regexp.    
     *)
    val string_to_regexp : string -> regexp

    (* ------------------------------------------------- *)
    (* Given a regular expression as string, parses it and returns 
       the equivalent nfa 
     *)
    val string_to_nfa: string -> nfa

    (* ------------------------------------------------- *)
    (* Throw IllegalExpression expression when regular
       expression syntax is illegal
     *)
    exception IllegalExpression of string

end

(* ------------------------------------------------- *)
(* MODULE IMPLEMENTATION *)
(* ------------------------------------------------- *)

    (* Make all your code changes past this point *)
    (* You may add/delete/reorder code as you wish 
       (but note that it still must match the signature above) *)

module NfaImpl =
struct

type transition = int * char option * int

type nfa = {ss : int; fs : int list; ts : transition list}

(* Next function given to us from class *)
let next = 
  let count = ref 0 in
    function () -> let temp = !count in
      count := (!count) + 1;
      temp
;;

(* Helper Methods from last project 
    TODO: Remove if not useful *)
let rec map f l = match l with
    [] -> []
  | (h::t) -> (f h)::(map f t)
;;

let rec fold f a l = match l with
    [] -> a
  | (h::t) -> fold f (f a h) t
;;

let length x = fold (fun a y -> a+1) 0 x
;;

let rev x = fold (fun a y -> y::a) [] x
;;

(* Index :-> Returns index of Value v in List x 
             Returns -1 if Value not found in list *)
let index list_x val1 =
   let rec rec_index list_x val1 pos =
      match list_x with
        [] -> -1 (* v not present *)
        | h::t when h = val1 -> pos (* v found, return index *)
        | h::t when h != val1 -> (* value not found *)
          let inc_pos = pos + 1 in (* increase position *)
          rec_index t val1 inc_pos (* recurse call on next elem (t) *)
      in
        rec_index list_x val1 0
;;

(* Find_unique :-> Finds unique elements in List x *)
let rec find_unique x = 
    match x with
      [] -> [] (* empty list *)
      | h::t when index t h = -1 -> (* curr index is unique *)
        let u_tl = find_unique t in
          h::u_tl (* keep curr index and append with recur *)
      | h::t when index t h != -1 -> (* curr index is not unique *)
        find_unique t (* throw away curr index and recur *)
                      (* TODO: Fix so List.sort_uniq works here might be able to 
                                remove entire find_unique method *)
;;

(* Make_Nfa :-> Returns NFA we can manipulate 
                and access members *)
let make_nfa ss fs ts = {ss = ss; fs = fs; ts = ts}
;; 

(* E_closure :-> Returns list of moves accessable by 
                  Epsilon Transitions *)
let rec e_closure m ss = 
  let rec find_closure nfa_x ss = 
    match ss with
    [] -> []
    | h::t -> 
      let fc_helper s_st f_st tr_list = 
        match tr_list with
        (x, y, z) when x = s_st && y = None -> s_st::z::f_st 
        | (x, y, z) when (x = s_st && y != None) || (x != s_st && y = None) -> s_st::f_st 
        | (x, y, z) when x != s_st && y != None -> f_st
      in
        (* Variables to hold data for Function calls *)
        let f_close_tl = find_closure m t in (* recurse on tail *)
        let f_close_hd = fc_helper h in (* e transitions on head *)
        let fold_list = List.fold_left f_close_hd [] m.ts in (* fold_left *)
        let h_fold = h::fold_list in (* add head to folded list *)
        let f_list_val = List.append h_fold f_close_tl in (* append our closures to our new list *)
          find_unique f_list_val (* return the list of unique values : removes dupes *)
  in
    (* TODO: Fix the crazyness here for readability *)
    if find_closure m ss = find_closure m (find_closure m ss) then 
      List.fast_sort compare (find_closure m ss) (* sort our list using List.sort's compare *)
    else e_closure m (find_closure m ss) (* recurse *)
;;


(* Moves on all possible transitons of a given letter for the given start state *)
let rec move m ss c = 
  let rec find_moves m ss c = 
    match ss with
      [] -> []
      | h::t -> 
        let parse_moves start_s final_s trans_l1 trans_l2 = 
          match trans_l2 with
            (x, y, z) when x != start_s || (x = start_s && y = None) -> trans_l1
            | (x, y, z) when x = start_s && y != None -> match y with Some b ->  
                if b = final_s then z::trans_l1 else trans_l1
        in
          (* Variables to hold function calls *)
          let pm_head = parse_moves h c in (* find moves for head *)
          let fm_tail = find_moves m t c in (* recur on tail to find rest of moves *)
          let lst_fold = List.fold_left pm_head [] m.ts in (* Fold pm_head with trans *)
          let f_list = List.append lst_fold fm_tail in (* Append fm_tail to lst_fold *)
            find_unique f_list (* Remove Dupes *)
  in
    let f_move = find_moves m ss c in 
      List.sort compare f_move (* Sort List using compare *)
;;

let accept m s = 
  (* Check for final state *)
  let rec is_final_state x y = 
    match y with
      [] -> false
      | h::t when index x h = -1 -> is_final_state x t (* Recur on tail *)
      | h::t when index x h > -1 || index x h < -1 -> true 
  in
    let rec parse_string m str ss ind =  
      (* Variables *)
      let s_len = String.length str - 1 in  (* get length of string *)
      let e_clo1 = e_closure m ss in 
      let m_clo1 = move m e_clo1 str.[ind] in
      let em_clo1 = e_closure m m_clo1 in
        if ind = s_len then  (* compare ind with string length *)
          em_clo1
        else 
          let inc_ind = ind + 1 in (* increase ind *)
            parse_string m str em_clo1 inc_ind
    in
      let temp = 
        if s = "" then e_closure m [m.ss] (* if s is empty call temp = eclosure *)
        else parse_string m s [m.ss] 0 (* s not empty check each *)
      in 
        is_final_state m.fs temp (*    *)
;;

type regexp =
	  Empty_String
	| Char of char
	| Union of regexp * regexp
	| Concat of regexp * regexp
	| Star of regexp

(* Regex to String *)
let rec regexp_to_string r = 
  match r with
    Empty_String -> "E"
    | Char c -> String.make 1 c
    | Union (a, b) -> 
      let con_regexp1 = regexp_to_string (a : regexp) in
      let con_regexp2 = regexp_to_string (b : regexp) in 
        String.concat " " [con_regexp1; con_regexp2; "|"]
    | Concat (a, b) -> 
      let con_regexp1 = regexp_to_string (a : regexp) in
      let con_regexp2 = regexp_to_string (b : regexp) in 
        String.concat " " [con_regexp1; con_regexp2; "."]
    | Star a -> 
      let con_regexp1 = regexp_to_string (a : regexp) in 
        String.concat " " [con_regexp1; "*"]
;;

(* Creates the transitions *)
let rec create_trans list_a var1 =
  match list_a with
    [] -> []
    | h::t -> 
      let head_t = (h, None, var1) in
      let tail_t = create_trans t var1 in (* Recurse Tail *)
        (* Append Trans Lists *)
        List.append [head_t] tail_t
;;

(* Create Union *)
let create_union val1 val2 nfa1 nfa2 = 
  let f_list = [val2] in
  let temp1 = (val1, None, nfa1.ss) in
  let temp2 = (val1, None, nfa2.ss) in
  (* Transitions *)
  let t_list1 = create_trans nfa1.fs val2 in
  let t_list2 = create_trans nfa2.fs val2 in
  (* Appending Lists *)
  let list_App = List.append nfa1.ts nfa2.ts in
  let list_App2 = List.append t_list1 t_list2 in
  let list_App3 = List.append list_App2 list_App in
  let list_App4 = List.append [temp1; temp2] list_App3 in
    (* Create our new Nfa *)
    make_nfa val1 f_list list_App4 
;;

(* Create Concatenation *)
let create_concat val1 val2 nfa1 nfa2=
  let t_list = create_trans nfa1.fs nfa2.ss in
  (* Appending Lists *)
  let list_App = List.append nfa1.ts nfa2.ts in
  let list_App2 = List.append t_list list_App in
    (* Create our new Nfa *)
    make_nfa nfa1.ss nfa2.fs list_App2
;;

(* Create Star *)
let create_star val1 val2 nfa1 = 
  (* Trans Lists *)
  let t_list = (val1, None, val2) in
  let t_list2 = (val2, None, val1) in
  let t_list3 = (val1, None, nfa1.ss) in 
  let t_list4 = create_trans nfa1.fs val2 in
  (* Appending Lists *)
  let list_App = List.append t_list4 nfa1.ts in
  let list_App2 = List.append [t_list3] list_App in
  let list_App3 = List.append [t_list; t_list2] list_App2 in
    (* Create our new Nfa *)
    make_nfa val1 [val2] list_App3
;;

(* Regexp to NFA *)
let rec regexp_to_nfa r = 
  (* Get 2 values using next function *)
  let val1 = next() in 
  let val2 = next() in
  match r with
    Empty_String ->
      let transList = (val1, None, val2) in
      let f_list = [val2] in
        make_nfa val1 f_list [transList]
    | Char c -> 
      let transList = (val1, Some c, val2) in
      let f_list = [val2] in
        make_nfa val1 f_list [transList]
    | Union (a, b) -> 
      let nfa_a = regexp_to_nfa (a : regexp) in
      let nfa_b = regexp_to_nfa (b : regexp) in
        create_union val1 val2 nfa_a nfa_b
    | Concat (a, b) ->
      let nfa_a = regexp_to_nfa (a : regexp) in
      let nfa_b = regexp_to_nfa (b : regexp) in
        create_concat val1 val2 nfa_a nfa_b
    | Star a -> 
      let nfa_a = regexp_to_nfa (a : regexp) in
        create_star val1 val2 nfa_a 
;;

exception IllegalExpression of string

(************************************************************************)
(* PARSER. You shouldn't have to change anything below this point *)
(************************************************************************)

(* Scanner code provided to turn string into a list of tokens *)

type token =
   Tok_Char of char
 | Tok_Epsilon
 | Tok_Union
 | Tok_Star
 | Tok_LParen
 | Tok_RParen
 | Tok_END

let re_var = Str.regexp "[a-z]"
let re_epsilon = Str.regexp "E"
let re_union = Str.regexp "|"
let re_star = Str.regexp "*"
let re_lparen = Str.regexp "("
let re_rparen = Str.regexp ")"

let tokenize str =
 let rec tok pos s =
   if pos >= String.length s then
     [Tok_END]
   else begin
     if (Str.string_match re_var s pos) then
       let token = Str.matched_string s in
       (Tok_Char token.[0])::(tok (pos+1) s)
	 else if (Str.string_match re_epsilon s pos) then
       Tok_Epsilon::(tok (pos+1) s)
	 else if (Str.string_match re_union s pos) then
       Tok_Union::(tok (pos+1) s)
	 else if (Str.string_match re_star s pos) then
       Tok_Star::(tok (pos+1) s)
     else if (Str.string_match re_lparen s pos) then
       Tok_LParen::(tok (pos+1) s)
     else if (Str.string_match re_rparen s pos) then
       Tok_RParen::(tok (pos+1) s)
     else
       raise (IllegalExpression "tokenize")
   end
 in
 tok 0 str

(* 
  A regular expression parser. It parses strings matching the 
  context free grammar below.

   S -> A Tok_Union S | A
   A -> B A | B
   B -> C Tok_Star | C
   C -> Tok_Char | Tok_Epsilon | Tok_LParen S Tok_RParen 

   FIRST(S) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(A) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(B) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(C) = Tok_Char | Tok_Epsilon | Tok_LParen
 *)

let lookahead tok_list = match tok_list with
	[] -> raise (IllegalExpression "lookahead")
	| (h::t) -> (h,t)

let rec parse_S l = 
	let (a1,l1) = parse_A l in
	let (t,n) = lookahead l1 in
	match t with 
		Tok_Union -> (
		let (a2,l2) = (parse_S n) in
		(Union (a1,a2),l2) 
		)
		| _ -> (a1,l1)

and parse_A l =
	let (a1,l1) = parse_B l in
	let (t,n) = lookahead l1 in
	match t with
	Tok_Char c ->
		let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2) 
	| Tok_Epsilon ->
		let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2) 
	| Tok_LParen -> 
		let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2) 
	| _ -> (a1,l1)

and parse_B l =
	let (a1,l1) = parse_C l in
	let (t,n) = lookahead l1 in
	match t with
	Tok_Star -> (Star a1,n) 
	| _ -> (a1,l1)

and parse_C l =
	let (t,n) = lookahead l in
	match t with
   	  Tok_Char c -> (Char c, n)
	| Tok_Epsilon -> (Empty_String, n)
	| Tok_LParen -> 
		let (a1,l1) = parse_S n in
		let (t2,n2) = lookahead l1 in
		if (t2 = Tok_RParen) then
			(a1,n2)
		else
			raise (IllegalExpression "parse_C 1")
	| _ -> raise (IllegalExpression "parse_C 2")

let string_to_regexp str = 
	let tok_list = tokenize str in
	let (a,t) = (parse_S tok_list) in
	match t with
	[Tok_END] -> a
	| _ -> raise (IllegalExpression "string_to_regexp")

let string_to_nfa s = regexp_to_nfa (string_to_regexp s)

end

module Nfa : NFA = NfaImpl;;
