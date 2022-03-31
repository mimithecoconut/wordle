(* Part A. *)

val list_of_string : string -> char list
val remove_exact_matches : char list -> char list -> char list * char list
val remove_exact_matches' : char list -> char list -> char list * char list
val find_and_remove_char : char -> char list -> char list option
val get_matches : char list -> char list -> char list
val get_letter_colors : string -> string list -> (char * char) list
val gray_codes : int -> int list list 

(* Part B. *)

type tree = Leaf | Node of int * int * tree * tree
val depth : tree -> int
val data : tree -> int
val make_node : int -> tree -> tree -> tree
val min_avl_tree : tree -> int option
val max_avl_tree : tree -> int option
val is_avl_tree : tree -> bool
val search : int -> tree -> bool
val left_rotate : tree -> tree
val right_rotate : tree -> tree
val insert : int -> tree -> tree 
