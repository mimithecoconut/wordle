(* name: Shenyi Li *)
(* email: sli5@caltech.edu *)

(*Part A*)
(*1*)
let list_of_string s = 
  let rec helper ls s i = 
    match i with
    |_ when i >= (String.length s) -> ls
    |_ -> s.[i] :: helper ls s (i+1) 
  in
  helper [] s 0

(*2*)
(*Recursive*)
let remove_exact_matches ls1 ls2 = 
  let get1 (a,_) = a in
  let get2 (_,a) = a in
  let rec helper ls1 ls2 =
    match (ls1, ls2) with 
    |([],_::_) -> failwith "remove_exact_matches: lists of different lengths"
    |(_::_, []) -> failwith "remove_exact_matches: lists of different lengths"
    |([],[]) -> ([], [])
    |(h1 :: t1, h2 :: t2) when h1 == h2 -> 
      let matches = (helper t1 t2) in
      ('_' :: get1 matches, '_' :: get2 matches)
    |(h1 :: t1, h2 :: t2) -> 
      let matches = (helper t1 t2) in
      (h1 :: get1 matches, h2 :: get2 matches)
  in 
  helper ls1 ls2

(*Note as stated in the midterm for asymptotic time complexity analysis, 
we provide the worst case. *)
(* Assuming that both lists have the same length n. We make n recursive 
calls since we go down both lists at the same time until we reach the point 
when we reach the end of the list and then recurse back. Adding and lookups 
only take 0(1) time. So overall, the worst case asymtotic time complexity 
for the recursive function is O(n). *)

(*Iterative*)
let remove_exact_matches' ls1 ls2 = 
  let get1 (a,_) = a in
  let get2 (_,a) = a in
  let rec iter ls1 ls2 ans =
    match (ls1, ls2) with 
    |([],_::_) -> failwith "remove_exact_matches: lists of different lengths"
    |(_::_, []) -> failwith "remove_exact_matches: lists of different lengths"
    |([],[]) -> (List.rev (get1 ans), List.rev (get2 ans))
    |(h1 :: t1, h2 :: t2) when h1 == h2 -> 
      iter t1 t2 ('_' :: get1 ans, '_' :: get2 ans) 
    |(h1 :: t1, h2 :: t2) -> iter t1 t2 (h1 :: get1 ans, h2 :: get2 ans) 
  in 
  iter ls1 ls2 ([],[])

(*For the iterative function, we look at the head of the list each time
until we reach the end of the list with lookups and adding all take O(1) time. 
At the very end, we reverse the lists which takes at worst O(n) time. But since 
this list reversal is done independently after the list traversal, the worst 
case asymtotic time complexity still falls under O(n).*)

(*3*)
(*Iterative*)
let find_and_remove_char c ls = 
  let rec iter c found ansls = function
    |[] when found -> Some (List.rev ansls)
    |[] -> None
    |h :: t when h == c && found == false -> iter c true ('_' :: ansls) t
    |h :: t -> iter c found (h::ansls) t
  in
  iter c false [] ls

(*In this iterative approach, we check if each of the values of the list matches
with c. This is O(n) where n is the length of the list. And the reversing of the
list is O(n). So, overall we have the worst case asymtotic time complexity of O(n).*)

(*4*)
(*ls1 target and ls2 guess*)
let get_matches ls1 ls2 = 
  let get1 (a,_) = a in
  let get2 (_,a) = a in 
  (*use to get the list from the list option*)
  let contents a = 
    match a with
    |Some x -> x 
    |_ -> failwith "not Some"
  in
  (*Recursive helper*)
  let rec helper ls1 ls2 = 
    match ls2 with 
    |[] -> [] 
    |h :: t when h == '_' -> 'G' :: (helper ls1 t) 
    |h :: t when find_and_remove_char h ls1 == None ->
       'B' :: (helper ls1 t)
    |h :: t -> 'Y' :: (helper (contents (find_and_remove_char h ls1)) t)
  in
  (*use remove_exact_matches function above, will already deal with error of 
  having different lengths*)
  let with_matches = remove_exact_matches ls1 ls2 in
  helper (get1 with_matches) (get2 with_matches)
  
(*First, we know that remove_exact_matches has time complexity of O(n). Then in the 
recursive helper the worst case is if we need to call find_and_remove_char which 
would require O(n) time to check if the character exists and replace it. Thus, 
overall, we have a O(n^2) worst case asymtotic time complexity. *)

(*5*)
let get_letter_colors targ gs =  
  let t_ls = list_of_string targ in 
  (*make the list of strings into a tuple list where each letter is paired 
  with the corresponding color*)
  let rec get_tuple_list targ = function 
    |[] -> []
    |h :: t -> let h_ls = list_of_string h in 
        List.combine h_ls (get_matches t_ls h_ls) @ get_tuple_list targ t
  in 
  (*returns true only if b has strictly higher priority than a *)
  let priority a b =
    match b with
    |'G' when a == 'B' || a == 'Y' -> true
    |'Y' when a == 'B' -> true 
    |_ -> false 
  in
  let dif_letter a b = (a != b  && a != '_') in 
  (*Recursive helper that only takes the tuple of a letter with highest 
  priority for the final answer*)
  let rec helper pre_let pre_col = function 
    |[] when pre_let != '_' -> (pre_let, pre_col) :: [] 
    |[] -> []
    |(a, b) :: t when dif_letter pre_let a -> 
      (pre_let, pre_col) :: (helper a b t)
    |(a, b) :: t when priority pre_col b -> helper a b t 
    |(a, b) :: t -> helper a pre_col t
  in
  helper '_' 'B' (List.sort compare (get_tuple_list targ gs))
            

(*6*)
let rec gray_codes n = 
  match n with
  |_ when n < 1 -> invalid_arg "gray_codes"
  |1 -> [[0]; [1]]
  |_ -> List.map (fun x -> (0 :: x) ) (gray_codes (n-1)) @ 
        List.map (fun x -> (1 :: x) ) (List.rev (gray_codes (n-1))) 


(*Part B*)
(*Given definitions and functions*)
type tree =
  | Leaf
  | Node of int * int * tree * tree   (* depth, value, left/right subtrees *)

  (* Depth of an AVL tree. *)
let depth = function
| Leaf -> 0
| Node (d, _, _, _) -> d

(* Extract the data value from a node. *)
let data = function
| Leaf -> failwith "no data"
| Node (_, v, _, _) -> v

(* Create a new node from two subtrees and a data value.
* This assumes that the ordering invariant holds i.e.
* that v is greater than any value in the left subtree
* and is smaller than any value in the right subtree.  *)
let make_node v l r =
let d = 1 + max (depth l) (depth r) in  (* compute the correct depth *)
  Node (d, v, l, r)

(* Find the minimum value in an AVL tree. *)
let rec min_avl_tree = function
  | Leaf -> None
  | Node (_, v, l, _) ->
    begin
      match min_avl_tree l with
        | None -> Some v
        | Some l' -> Some l'
    end

(* Find the maximum value in an AVL tree. *)
let rec max_avl_tree = function
  | Leaf -> None
  | Node (_, v, _, r) ->
    begin
      match max_avl_tree r with
        | None -> Some v
        | Some r' -> Some r'
    end

(* Return true if a tree is a valid AVL tree. *)
let rec is_avl_tree = function
  | Leaf -> true
  | Node (d, v, l, r) ->
    let dl = depth l in
    let dr = depth r in
    if is_avl_tree l
      && is_avl_tree r
      && d = 1 + max dl dr
      && abs (dl - dr) < 2
      then  (* check order invariant *)
        match (max_avl_tree l, min_avl_tree r) with
          | (None, None) -> true
          | (None, Some rmin) -> v <= rmin
          | (Some lmax, None) -> v >= lmax
          | (Some lmax, Some rmin) -> v >= lmax && v <= rmin
      else false

(*1*)
let search v t = 
  let rec helper v t found = 
    match t with 
    |Leaf -> found 
    |Node (_, a, l, r) when a == v -> (helper v l true) || (helper v r true)
    |Node (_,_,l,r) -> (helper v l found) || (helper v r found)
  in
  helper v t false 

(*2*)

let left_rotate = function
  |Node (d1, v1, l1 , Node (d2, v2, l2, r2)) -> 
    make_node v2 (make_node v1 l1 l2) r2
  |Node (_, _, _, _) -> failwith "can't be left rotated"
  |Leaf -> failwith "can't be left rotated"
  

let right_rotate = function
  |Node (d1, v1, Node (d2, v2, l2, r2), r1) -> 
    make_node v2 l2 (make_node v1 r2 r1) 
  |Node (_, _, _, _) -> failwith "can't be right rotated"
  |Leaf -> failwith "can't be right rotated"

(*3*)

let rec insert v t =
  match t with
    | Leaf -> Node (1, v, Leaf, Leaf)  (* base case *)
    | Node (_, v', l, r) ->
      begin
        match () with
          | _ when v < v' ->   (* insert into left subtree *)
            let l' = insert v l in  (* new left subtree *)
              if depth l' - depth r = 2  (* tree is now unbalanced *)
                then
                  if v < data l'
                    then  (* left-left case *)
                      (* new value v is in the left subtree of l';
                         need to do a right rotation of the new tree *)
                      right_rotate (make_node v' l' r)
                    else  (* left-right case *)
                      (* new value v is in the right subtree of l';
                         need to do a left rotation on l'
                         and a right rotation on the resulting tree. *)
                      let l_rot = left_rotate l' in 
                      right_rotate (make_node v' l_rot r)
                else
                  make_node v' l' r  (* already balanced *)
          | _ when v > v' ->   (* insert into right subtree *)
              let r' = insert v r in  (* new right subtree *)
              if depth r' - depth l = 2  (* tree is now unbalanced *)
                then
                  if v > data r'
                    then  (* right-right case *)
                      (* new value v is in the right subtree of r';
                         need to do a left rotation of the new tree *)
                      left_rotate (make_node v' l r')
                    else  (* right-left case *)
                      (* new value v is in the left subtree of r';
                         need to do a right rotation on r'
                         and a left rotation on the resulting tree. *)
                      let r_rot = right_rotate r' in
                      left_rotate (make_node v' l r_rot)
                else
                  make_node v' l r'  (*already balanced*)
          | _ -> t  (* already in tree *)
      end