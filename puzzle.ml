(* CMSC 330 / Project 3 *)
(* Student: Harry Young *)
(* UID: Hyoung12 *)
(* Fill in the implementation and submit puzzle.ml *)

#use "testUtils.ml";;

(*-------------------------------------------------------------------------*)
(* functions from lecture you may use *)

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

(*-------------------------------------------------------------------------*)
(* Part 1: Recursion *)

(* 
get_val x n 	
int list -> int -> int 	
element of list x at index n, or -1 if not found
  (indexes start at 0)
Example: get_val [5;6;7;3] 1 => 6
*)

let rec get_val x n = 
	if n < 0 || n >= (length x) then -1 (* check if n is in bounds *)
	else match x with 
	[] -> -1 (* elm not found *)
	| h::t when n > 0 -> get_val t (n-1) (* not correct index so rec call *)
	| h::t when n = 0 -> h (* elm found *)
;;

(* 
get_vals x y 	
int list -> int list -> int list 	
list of elements of list x at indexes in list y, 
[] if any indexes in y are outside the bounds of x;
elements must be returned in order listed in y 
Example: get_vals [5;6;7;3] [2;0] => [7;5]
*)

let get_vals x y =
  let rec gv_rec l m e =  (* l = list1 m = list2 e = list of elms *)
  match m with
  | [] -> e (* return elm list *)
  | h::t when (get_val l h) = -1 -> []
  | h::t when (get_val l h) != -1 -> 
  			let r = get_val l h in
           (gv_rec l t (r::e)) in rev (gv_rec x y [])  (* rev the list 
           													so we get right answer *)
;;

(* 
list_swap_val b u v
'a list -> 'a -> 'a -> 'a list 	
list b with values u,v swapped 	
(change value of multiple occurrences of u and/or v, if found, and
change value for u even if v not found in list, and vice versa )
Example: list_swap_val [5;6;7;3] 7 5 => [7;6;5;3]
*)

let rec list_swap_val b u v = 
	match b with
	[] -> []
	| h::t when h = u -> let x = (list_swap_val t u v) in
							v::x (* u -> v *)
	| h::t when h = v -> let x = (list_swap_val t u v) in
							u::x (* v -> u *)
 	| h::t when h != u && h != v -> let x = (list_swap_val t u v) in
 							h::x (* u/v not curr pos so move on *)
;;

(* 
index x v
'a list -> 'a -> int 	
index of value v in list x, or -1 if not found
  (indexes start at 0)
Example: index [5;6;7;3] 7 => 2
*)

let index x v =
  let rec index_rec l p = (* l = list p = pos *)
    match l with 
    | [] -> -1  (* v does not exist *)
    | h::t when h = v -> p (* return pos *)
    | h::t when h < v || h > v -> index_rec t (p + 1) in (* h != v increase counter *)
  		index_rec x 0  (* initialize counter to 0 *)
;;

(* 
distinct x
'a list -> 'a list 
return list of distinct members of list x 
*)

let rec is_elt l v =  (* l = list v = value *)
	match l with
	[] -> false
	| h::t when h = v -> true (* value found *)
	| h::t when h != v -> is_elt t v (* h!= value -> recurse *)
;;

let rec rem_val l v = (* l = list v = value *) 
	match l with
	[] -> []
	| h::t when h = v -> rem_val t v (* h found, remove it *)
    | h::t when h != v -> h::rem_val t v (* not at value -> recur *)
;;

let rec distinct x = 
	match x with
	[] -> []
	| h::t when (is_elt t h) = true -> distinct (rem_val t h) (* h not distinct, remove it, recur *)
	| h::t when (is_elt t h) = false -> h::distinct t (* h is distinct, add and recur *)
;;

(* remove x y
'a list -> int list -> 'a list
remove elements of list x at indexes in list y, return resulting list. 
Ignore indexes that are out of range. 
*)

(* removes any index with value -384 from x*)
let rec rem_val x = 
	match x with 
	[] -> []
	| h::t when h = -384 -> rem_val t (* h = -384 so delete *)
    | h::t when h < -384 || h > -384 -> h::rem_val t (* h != delete value *)
;;

(* set index(n) of x with v *)
let rec set_val x n v = 
	match x with
	[] -> []
	| h::t when n > 0 -> h::(set_val t (n-1) v) (* not correct index so recur *)
	| h::t when n = 0 -> v::t (* set index n = -384 *)
;;

let rec remove x y =
	(* recurses through y, changing correct indexes in x then removes them *)
	match y with 
	[] -> rem_val x (* call remove values to remove correct indexes *)
	| h::t -> let v = -384 in (* Remove Value *)
				let s = set_val x h v in remove s t 
;;

(* 
find_new x y
'a list -> 'a list -> 'a list 	
list of members of list x not found in list y 	
maintain relative order of elements in result
Example: find_new [4;3;7] [5;6;5;3] => [4;7]
*)

let rec find_new x y =
	match x with 
	[] -> []
	| h::t when (index y h) > -1 -> find_new t y  (* h is not unique *)
	| h::t when (index y h) = -1 -> h::find_new t y (* h is unique -> 
														add to list and recurse *)
;;

(* 
is_sorted x 	
'a list -> bool 	
true if elements in x are in sorted order, false otherwise 	
  (return true for [])
Example: is_sorted [5;5;7;9] => true 
*)

let rec is_sorted x = 
  match x with
  [] -> true
  | [h] -> true (* sorted if list only contains one item *)
  | h::t when h <= (get_val t 0) -> is_sorted t (* h < t -> check next values *)
  | h::t when h > (get_val t 0) -> false (* h > t -> not sorted *)
 ;;

(*-------------------------------------------------------------------------*)
(* Part 2: Higher order functions *)

(* 
grow_lists x y 	 
'a list -> 'a list -> 'a list list 	 
return a list of lists, where each element of x is prepended to y
resulting lists must be in same order as in x
Example: grow_lists [1;2] [3;4] => [[1;3;4]; [2;3;4]]
*)

let grow_lists x y = 
	map (fun a -> a::y) x (* call map with simple prepend function 
							that maps each element x to y-list *)
;;

(* 
concat_lists x 	
'a list list -> 'a list 	
return a list consisting of the lists in x concatenated together
(note just top level of lists is concatenated, unlike List.flatten)
Examples: concat_lists [[1;2];[7];[5;4;3]] => [1;2;7;5;4;3]
concat_lists [[[1;2;3];[2]];[[7]]] => [[1;2;3];[2];[7]]
*)

let concat_lists x = 
  fold (@) [] x  (* fold with concat operator *)
;; 

(*-------------------------------------------------------------------------*)
(* Part 3: Puzzle functions *)

(* 
find_board_size b 	 
'a list -> int 	 
return size (that is, the length/width of a side) of board b 
represented as a list (assume board is square)
Example: find_board_size [1;0;2;3;4;5;6;7;8] => 3
*)

let find_board_size b = int_of_float(sqrt(float(length b)))
;;

(* 
pos_of_xy (x, y) s 	
(int * int) -> int -> int 	
index of x, y coordinate in a list representing a board of size s
return -1 if x or y is out of bounds (i.e., less than 0 or greater than s-1)
Example: pos_of_xy (2, 1) 3 => 5
*)

let pos_of_xy (x, y) s =
	if (x < 0 || x > (s-1) || y < 0 || y > (s-1)) then 
	(-1) (* if x or y is out of bounds *)
	else (y * s) + x  (* calculate position *)
;;

(* 
xy_of_pos p s 	
int -> int -> (int * int)
x, y coordinate of index p in a list representing a board of size s
may assume p is a legal position between 0..s-1
Example: xy_of_pos 5 3 => (2, 1)
*)

let xy_of_pos p s =
	((p - s * (p / s)) , (p / s))
;;

(* 
move_pos b 	
int list -> int list 	
list of positions in board that can move to space in board
positions must be in sorted order, from smallest to largest
Example: move_pos [0;1;2;3;4;5;6;7;8] => [1;3]
*)

let move_pos b = 
	(* variables for use in rec call *)
	let l = length b in  (* length of board *)
	let i = index b 0 in  (* find where space is *)
	let s = find_board_size b in  (* get board size *)
  	let rec mp_rec x = 
  		match x with
  		[] -> []
  		| h::t when h < 0 || h >= l -> mp_rec t (* h out of bounds -> remove it *)
  		| h::t when h >= 0 && h < l -> h::mp_rec t in  (* h is in bounds *)
  			(* find surrounding values that can move into space *)
  			if (i mod s) = 0 then
    			mp_rec [i - s; i + 1; i + s] (* space is on (left/lower) edge *)
  			else if ((i+1) mod s) = 0 then
    			mp_rec [i - s; i - 1; i + s] (* space is on (right/Upper) Edge *)
  			else mp_rec [i - s; i - 1; i + 1; i + s] (* space is not on an edge of board *)
;;

(* 
make_move b x 	
int list -> int -> int list 	
configuration of board after moving number at position x to space
may assume position x is adjacent to space
Example: make_move [0;1;4;5;2;3;6;7;8] 3 => [5;1;4;0;2;3;6;7;8] 
*)

let make_move b x = 
	let a = get_val b x in (* get x's value *)
  	list_swap_val b a 0 (* swap with open space *)
;;

(* 
make_moves b 	
int list -> int list list 	
boards produced after all possible 1-step moves for board b
boards must be in sorted order, with space in smallest position to largest
Example: make_moves [0;1;2;3;4;5;6;7;8] => 
	[[1;0;2;3;4;5;6;7;8];[3;1;2;0;4;5;6;7;8]] 
*)

let make_moves b = 
  let rec mmoves_rec x = 
      match x with
      [] -> []
      | h::t -> make_move b h::mmoves_rec t in 
      			mmoves_rec (move_pos b)
;;

(* 
single_move x
int list list list -> int list list list
Given list of list of boards, return list of list of boards,
with 1-step move (for head of each list of boards L) prepended to L.
If n 1-step moves (M_1,M_2,...M_n) are possible for the head 
of board list L, then M_1::L, M2_2::L,...M_n::L should all
be added to the result.

Example: single_move [[[0;1;2;3]]] => 
	[ [[1;0;2;3];[0;1;2;3]] ; [[2;1;0;3];[0;1;2;3]] ]
*)

let mov_head x =
	match x with
	[] -> []
	| h::t -> let y = make_moves h in 
		grow_lists y x (* makes move on head then maps it to list sent in *)
;;

let rec single_move x =  
  	match x with
  	[] -> []
  	| h::t -> mov_head h @ single_move t (* make single move on head, prepend
  											to rec call with tail *)
;;

(*-------------------------------------------------------------------------*)
(* Part 4: Puzzle solver *)

let solve_board b n =
   let rec sol_rec x =
   	match x with
      [] -> []  (* empty list *)
      | h::t when is_sorted h = true -> [x] (* return board if already solved *)
      | h::t when is_sorted h = false -> (* not solved yet *)
         if length x > n || index t h > 0 then [] (* if solution > n OR not unique 
         											solution :: delete it *)
         else (* variables set to function values to call concat *)
         	let r = make_moves h in 
         	let s = grow_lists r (h::t) in
         	let p = map sol_rec s in 
            concat_lists p in sol_rec [b]
;;

(* 
solve_board b n
int list -> int -> int list list list

Given board b, return all solutions of length n, or [] if none exists.
A solution to solve_board is a list of boards produced by moves
starting from b until the solved board is reached.  The list is in
reverse order: solved board first, b last.  

Example: solve_board [1;2;0;3;4;5;6;7;8] 2 => 
	[[[0;1;2;3;4;5;6;7;8];[1;0;2;3;4;5;6;7;8];[1;2;0;3;4;5;6;7;8]]]

The length L of each solution is the number of moves (i.e., one less
than the length of the list that represents the solution).  Solutions
are not permitted to contain the same intermediate board twice.  For
example, [[[0;1;2;3;4;5;6;7;8];[1;0;2;3;4;5;6;7;8];[0;1;2;3;4;5;6;7;8];
[1;0;2;3;4;5;6;7;8];[1;2;0;3;4;5;6;7;8]]] is not a legal length-4 
solution to [1;2;0;3;4;5;6;7;8]. The order of possible solutions does 
not matter.
 
Hints: as you are required to produce *all* solutions up to length n,
you are essentially doing an exhaustive search with a bit of smarts to
prune out paths containing duplicate boards.  That is, at each step
you will want to enumerate all possible boards produced by legal moves
from the current board of each path produced by prior steps.  You will
prune out paths that would be produced by repeating a previous board
position.  You should be making good use of the functions you have
already defined above.  If your solution is not using many of these
functions, you are doing too much work! *)


(*-------------------------------------------------------------------------*)
(* Bonus debugging utilities *)

(* print board as nXn square, with space @ 0 *)
let print_board b = 
    let board_size = (find_board_size b) in 
    let rec print_board_helper (b, x) = match b with
	  [] -> print_endline "------------------------"
	| (h::t) -> 
		print_string (if (h < 10) then "   " 
			else if (h < 100) then "  " else " ");
		if (h = 0) then print_string " " else (print_int h) ; 
		(if ((x mod board_size) = 0) then print_endline "") ; 
		print_board_helper (t, x+1)
    in print_board_helper (b, 1)
;;

(* print list of boards *)
let print_boards x = 
	print_endline "------------------------" ;
	ignore (map print_board x) ;
	print_endline ""
;;

(* print some boards & lists of boards *)

(* uncomment following to test print! *)
(*
let try_out_print =
	let b1 = [0;1;2;3;4;5;6;7;8] in
	let b2 = [1;0;2;3;4;5;6;7;8] in
	let blist = [b1;b2] in
		prt_int_list b1;
		print_board b1;
		prt_int_list b2;
		print_board b2;
		prt_int_list_list blist;
		print_boards blist
;;
*)

