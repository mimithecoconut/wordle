open OUnit2
open Midterm

(*
 * Utilities.
 *)

let assert_raises_failure msg x =
  assert_bool msg
    (try
       begin
          ignore (x ());
          false
       end
     with
       | Failure _ -> true
       | _ -> false)

let assert_raises_invalid_arg msg x =
  assert_bool msg
    (try
       begin
          ignore (x ());
          false
       end
     with
       | Invalid_argument _ -> true
       | _ -> false)

(* Some sample trees. *)

let t1  = Node (2, 35, Leaf, Node (1, 42, Leaf, Leaf))
let t1' = Node (2, 42, Node (1, 35, Leaf, Leaf), Leaf)

let t2  = Node (2, 35, Node (1, 42, Leaf, Leaf), Leaf)
let t2' = Node (2, 42, Leaf, Node (1, 35, Leaf, Leaf))

let t3  = Node (3, 21, Leaf, Node (2, 35, Leaf, Node (1, 42, Leaf, Leaf)))
let t3' = Node (2, 35, Node (1, 21, Leaf, Leaf), Node (1, 42, Leaf, Leaf))

let t4  = Node (3, 21, Node (2, 35, Node (1, 42, Leaf, Leaf), Leaf), Leaf)
let t4' = Node (2, 35, Node (1, 42, Leaf, Leaf), Node (1, 21, Leaf, Leaf))

let tree0 = Leaf
let tree1 = Node (1, 6, Leaf, Leaf)
let tree2 = Node (2, 6, Node (1, 3, Leaf, Leaf), Leaf)
let tree3 =
  Node (2, 3, Node (1, 1, Leaf, Leaf), Node (1, 6, Leaf, Leaf))
let tree4 =
  Node (3, 3, Node (1, 1, Leaf, Leaf),
   Node (2, 6, Node (1, 4, Leaf, Leaf), Leaf))
let tree5 =
  Node (3, 3, Node (1, 1, Leaf, Leaf),
   Node (2, 5, Node (1, 4, Leaf, Leaf), Node (1, 6, Leaf, Leaf)))
let tree6 =
  Node (3, 5, Node (2, 3, Node (1, 1, Leaf, Leaf), Node (1, 4, Leaf, Leaf)),
   Node (2, 6, Leaf, Node (1, 10, Leaf, Leaf)))
let tree7 =
  Node (3, 5, Node (2, 3, Node (1, 1, Leaf, Leaf), Node (1, 4, Leaf, Leaf)),
   Node (2, 7, Node (1, 6, Leaf, Leaf), Node (1, 10, Leaf, Leaf)))
let tree8 =
  Node (4, 5, Node (2, 3, Node (1, 1, Leaf, Leaf), Node (1, 4, Leaf, Leaf)),
   Node (3, 7, Node (1, 6, Leaf, Leaf),
    Node (2, 10, Node (1, 8, Leaf, Leaf), Leaf)))
let tree9 =
  Node (4, 5, Node (2, 3, Node (1, 1, Leaf, Leaf), Node (1, 4, Leaf, Leaf)),
   Node (3, 7, Node (1, 6, Leaf, Leaf),
    Node (2, 9, Node (1, 8, Leaf, Leaf), Node (1, 10, Leaf, Leaf))))
let tree10 =
  Node (4, 5,
   Node (3, 3, Node (2, 1, Leaf, Node (1, 2, Leaf, Leaf)),
    Node (1, 4, Leaf, Leaf)),
   Node (3, 7, Node (1, 6, Leaf, Leaf),
    Node (2, 9, Node (1, 8, Leaf, Leaf), Node (1, 10, Leaf, Leaf)))) 

let all_tests = "all" >:::
[
  (* ----------------------------------------------------------------------
   * Part A.
   * ---------------------------------------------------------------------- *)

  "Problem A.1" >:: (fun _ ->
    assert_equal ~msg:"list_of_string 1"
      (list_of_string "quest") ['q'; 'u'; 'e'; 's'; 't'];
    assert_equal ~msg:"list_of_string 2"
      (list_of_string "") ([]);
    assert_equal ~msg:"list_of_string 3"
      (list_of_string "a") (['a']);
    assert_equal ~msg:"list_of_string 4"
      (list_of_string "ab") (['a'; 'b']);
    assert_equal ~msg:"list_of_string 5"
      (list_of_string "abc") (['a'; 'b'; 'c']);
  );

  "Problem A.2" >:: (fun _ ->
    assert_equal ~msg:"remove_exact_matches 1"
      (remove_exact_matches [] []) ([], []);

    assert_equal ~msg:"remove_exact_matches 2"
      (remove_exact_matches ['a'] ['a']) (['_'], ['_']);

    assert_equal ~msg:"remove_exact_matches 3"
      (remove_exact_matches ['a'; 'b'] ['b'; 'a']) (['a'; 'b'], ['b'; 'a']);

    assert_equal ~msg:"remove_exact_matches 4"
      (remove_exact_matches ['a'; 'a'; 'b'] ['a'; 'b'; 'a'])
      (['_'; 'a'; 'b'], ['_'; 'b'; 'a']);

    assert_equal ~msg:"remove_exact_matches 5"
      (remove_exact_matches ['a'; 'a'; 'b'] ['a'; 'a'; 'c'])
      (['_'; '_'; 'b'], ['_'; '_'; 'c']);

    assert_equal ~msg:"remove_exact_matches 6"
      (remove_exact_matches ['r'; 'e'; 'a'; 'c'; 't'] ['a'; 'b'; 'a'; 't'; 'e'])
      (['r'; 'e'; '_'; 'c'; 't'], ['a'; 'b'; '_'; 't'; 'e']);

    assert_raises_failure "remove_exact_matches 7"
      (fun () -> remove_exact_matches [] ['a']);

    assert_raises_failure "remove_exact_matches 8"
      (fun () -> remove_exact_matches ['a'] []);

    assert_equal ~msg:"remove_exact_matches' 1"
      (remove_exact_matches' [] []) ([], []);

    assert_equal ~msg:"remove_exact_matches' 2"
      (remove_exact_matches' ['a'] ['a']) (['_'], ['_']);

    assert_equal ~msg:"remove_exact_matches' 3"
      (remove_exact_matches' ['a'; 'b'] ['b'; 'a']) (['a'; 'b'], ['b'; 'a']);

    assert_equal ~msg:"remove_exact_matches' 4"
      (remove_exact_matches' ['a'; 'a'; 'b'] ['a'; 'b'; 'a'])
      (['_'; 'a'; 'b'], ['_'; 'b'; 'a']);

    assert_equal ~msg:"remove_exact_matches' 5"
      (remove_exact_matches' ['a'; 'a'; 'b'] ['a'; 'a'; 'c'])
      (['_'; '_'; 'b'], ['_'; '_'; 'c']);

    assert_equal ~msg:"remove_exact_matches' 6"
      (remove_exact_matches' ['r'; 'e'; 'a'; 'c'; 't'] ['a'; 'b'; 'a'; 't'; 'e'])
      (['r'; 'e'; '_'; 'c'; 't'], ['a'; 'b'; '_'; 't'; 'e']);

    assert_raises_failure "remove_exact_matches' 7"
      (fun () -> remove_exact_matches' [] ['a']);

    assert_raises_failure "remove_exact_matches' 8"
      (fun () -> remove_exact_matches' ['a'] []);
  );

  "Problem A.3" >:: (fun _ ->
    assert_equal ~msg:"find_and_remove_char 1"
      (find_and_remove_char 'c' ['a']) None;

    assert_equal ~msg:"find_and_remove_char 2"
      (find_and_remove_char 'c' ['c']) (Some ['_']);

    assert_equal ~msg:"find_and_remove_char 3"
      (find_and_remove_char 'c' ['c'; 'r'; 'a'; 'n'; 'e'])
      (Some ['_'; 'r'; 'a'; 'n'; 'e']);

    assert_equal ~msg:"find_and_remove_char 4"
      (find_and_remove_char 'c' ['a'; 'r'; 'o'; 's'; 'e']) None;

    assert_equal ~msg:"find_and_remove_char 5"
      (find_and_remove_char 'o' ['a'; 'r'; 'o'; 's'; 'e'])
      (Some ['a'; 'r'; '_'; 's'; 'e']);

    assert_equal ~msg:"find_and_remove_char 6"
      (find_and_remove_char 'e' ['a'; 'r'; 'o'; 's'; 'e'])
      (Some ['a'; 'r'; 'o'; 's'; '_']);

    assert_equal ~msg:"find_and_remove_char 7"
      (find_and_remove_char 'o' ['b'; 'o'; 'o'; 's'; 't'])
      (Some ['b'; '_'; 'o'; 's'; 't']);
  );

  "Problem A.4" >:: (fun _ ->
    assert_raises_failure
      "get_matches 1"
      (fun () -> get_matches ['a'] ['a'; 'b'; 'c']);

    assert_raises_failure
      "get_matches 2"
      (fun () -> get_matches ['a'; 'b'; 'c'] ['a']);

    assert_equal ~msg:"get_matches 3"
      (get_matches [] []) [];

    assert_equal ~msg:"get_matches 4"
      (get_matches ['a'] ['a']) ['G'];

    assert_equal ~msg:"get_matches 5"
      (get_matches ['a'] ['b']) ['B'];

    assert_equal ~msg:"get_matches 6"
      (get_matches ['a'; 'b'] ['b'; 'a']) ['Y'; 'Y'];

    assert_equal ~msg:"get_matches 7"
      (get_matches ['a'; 'a'; 'b'] ['b'; 'a'; 'a'])
      ['Y'; 'G'; 'Y'];

    assert_equal ~msg:"get_matches 8"
      (get_matches ['b'; 'a'; 'd'] ['a'; 'a'; 'b'])
      ['B'; 'G'; 'Y'];

    assert_equal ~msg:"get_matches 9"
      (get_matches ['a'; 'b'; 'a'; 'd'] ['b'; 'a'; 'b'; 'a'])
      ['Y'; 'Y'; 'B'; 'Y'];

    assert_equal ~msg:"get_matches 10"
      (get_matches ['r'; 'e'; 'a'; 'c'; 't'] ['c'; 'r'; 'a'; 'n'; 'e'])
      ['Y'; 'Y'; 'G'; 'B'; 'Y'];

    assert_equal ~msg:"get_matches 11"
      (get_matches ['a'; 'b'; 'a'; 't'; 'e'] ['c'; 'r'; 'a'; 'n'; 'e'])
      ['B'; 'B'; 'G'; 'B'; 'G'];

    assert_equal ~msg:"get_matches 12"
      (get_matches ['p'; 'r'; 'a'; 'n'; 'k'] ['a'; 'b'; 'a'; 't'; 'e'])
      ['B'; 'B'; 'G'; 'B'; 'B'];
  );
 
  "Problem A.5" >:: (fun _ ->

    assert_equal ~msg:"get_letter_colors 1"
      (get_letter_colors "react" [])
      [];

    assert_equal ~msg:"get_letter_colors 1"
      (get_letter_colors "react" ["crane"])
      [('a', 'G'); ('c', 'Y'); ('e', 'Y'); ('n', 'B'); ('r', 'Y')];

    assert_equal ~msg:"get_letter_colors 1"
      (get_letter_colors "react" ["crane"; "arose"])
      [('a', 'G'); ('c', 'Y'); ('e', 'Y'); ('n', 'B'); 
       ('o', 'B'); ('r', 'Y'); ('s', 'B')];

    assert_equal ~msg:"get_letter_colors 1"
      (get_letter_colors "react" ["crane"; "arose"; "quick"])
      [('a', 'G'); ('c', 'G'); ('e', 'Y'); ('i', 'B'); ('k', 'B'); ('n', 'B');
       ('o', 'B'); ('q', 'B'); ('r', 'Y'); ('s', 'B'); ('u', 'B')];

    assert_equal ~msg:"get_letter_colors 1"
      (get_letter_colors "react" ["crane"; "arose"; "quick"; "reach"])
      [('a', 'G'); ('c', 'G'); ('e', 'G'); ('h', 'B'); ('i', 'B'); ('k', 'B');
       ('n', 'B'); ('o', 'B'); ('q', 'B'); ('r', 'G'); ('s', 'B'); ('u', 'B')];

    assert_equal ~msg:"get_letter_colors 1"
      (get_letter_colors "react" ["crane"; "arose"; "quick"; "reach"; "react"])
      [('a', 'G'); ('c', 'G'); ('e', 'G'); ('h', 'B'); ('i', 'B'); ('k', 'B');
       ('n', 'B'); ('o', 'B'); ('q', 'B'); ('r', 'G'); ('s', 'B'); ('t', 'G');
       ('u', 'B')];

    assert_raises_failure "get_matches 7"
      (fun () -> get_letter_colors "react" ["cost"])
  );

  "Problem A.6" >:: (fun _ ->
    assert_raises_invalid_arg "gray_codes (-1)" (fun () -> gray_codes (-1));
    assert_raises_invalid_arg "gray_codes 0" (fun () -> gray_codes 0);
    assert_equal ~msg:"gray_codes 1" (gray_codes 1) [[0]; [1]];
    assert_equal ~msg:"gray_codes 2" (gray_codes 2) [[0;0]; [0;1]; [1;1]; [1;0]];
    assert_equal ~msg:"gray_codes 3" (gray_codes 3)
      [[0;0;0]; [0;0;1]; [0;1;1]; [0;1;0];
       [1;1;0]; [1;1;1]; [1;0;1]; [1;0;0]];
    assert_equal ~msg:"gray_codes 4" (gray_codes 4)
      [[0; 0; 0; 0]; [0; 0; 0; 1]; [0; 0; 1; 1]; [0; 0; 1; 0]; [0; 1; 1; 0];
       [0; 1; 1; 1]; [0; 1; 0; 1]; [0; 1; 0; 0]; [1; 1; 0; 0]; [1; 1; 0; 1];
       [1; 1; 1; 1]; [1; 1; 1; 0]; [1; 0; 1; 0]; [1; 0; 1; 1]; [1; 0; 0; 1];
       [1; 0; 0; 0]];
  ); 

  (* ----------------------------------------------------------------------
   * Part B.
   * ---------------------------------------------------------------------- *)

   "Problem B.1: search" >:: (fun c ->
    assert_bool "test0" (not (search 6 tree0));

    assert_bool "test1" (not (search 3 tree1));
    assert_bool "test1" (search 6 tree1);

    assert_bool "test2" (not (search 1 tree2));
    assert_bool "test2" (search 3 tree2);
    assert_bool "test2" (search 6 tree2);

    assert_bool "test3" (not (search 4 tree3));
    assert_bool "test3" (search 1 tree3);
    assert_bool "test3" (search 3 tree3);
    assert_bool "test3" (search 6 tree3);

    assert_bool "test4" (not (search 5 tree4));
    assert_bool "test4" (search 4 tree4);
    assert_bool "test4" (search 1 tree4);
    assert_bool "test4" (search 3 tree4);
    assert_bool "test4" (search 6 tree4);

    assert_bool "test5" (not (search 10 tree5));
    assert_bool "test5" (search 5 tree5);
    assert_bool "test5" (search 4 tree5);
    assert_bool "test5" (search 1 tree5);
    assert_bool "test5" (search 6 tree5);
    assert_bool "test5" (search 3 tree5);

    assert_bool "test6" (not (search 7 tree6));
    assert_bool "test6" (search 10 tree6);
    assert_bool "test6" (search 5 tree6);
    assert_bool "test6" (search 4 tree6);
    assert_bool "test6" (search 1 tree6);
    assert_bool "test6" (search 6 tree6);
    assert_bool "test6" (search 3 tree6);

    assert_bool "test7" (not (search 8 tree7));
    assert_bool "test7" (search 7 tree7);
    assert_bool "test7" (search 10 tree7);
    assert_bool "test7" (search 5 tree7);
    assert_bool "test7" (search 4 tree7);
    assert_bool "test7" (search 1 tree7);
    assert_bool "test7" (search 6 tree7);
    assert_bool "test7" (search 3 tree7);

    assert_bool "test8" (not (search 9 tree8));
    assert_bool "test8" (search 8 tree8);
    assert_bool "test8" (search 7 tree8);
    assert_bool "test8" (search 10 tree8);
    assert_bool "test8" (search 5 tree8);
    assert_bool "test8" (search 4 tree8);
    assert_bool "test8" (search 1 tree8);
    assert_bool "test8" (search 6 tree8);
    assert_bool "test8" (search 3 tree8);

    assert_bool "test9" (not (search 2 tree9));
    assert_bool "test9" (search 9 tree9);
    assert_bool "test9" (search 8 tree9);
    assert_bool "test9" (search 7 tree9);
    assert_bool "test9" (search 10 tree9);
    assert_bool "test9" (search 5 tree9);
    assert_bool "test9" (search 4 tree9);
    assert_bool "test9" (search 1 tree9);
    assert_bool "test9" (search 6 tree9);
    assert_bool "test9" (search 3 tree9);

    assert_bool "test10" (not (search 11 tree10));
    assert_bool "test10" (search 2 tree10);
    assert_bool "test10" (search 9 tree10);
    assert_bool "test10" (search 8 tree10);
    assert_bool "test10" (search 7 tree10);
    assert_bool "test10" (search 10 tree10);
    assert_bool "test10" (search 5 tree10);
    assert_bool "test10" (search 4 tree10);
    assert_bool "test10" (search 1 tree10);
    assert_bool "test10" (search 6 tree10);
    assert_bool "test10" (search 3 tree10);
  );

  "Problem B.2: rotate" >:: (fun c ->
    assert_equal (left_rotate t1) t1';
    assert_equal (right_rotate t2) t2'; 
    assert_equal (left_rotate t3) t3';
    assert_equal (right_rotate t4) t4'; 
  );

 "Problem B.3: insert" >:: (fun c ->
    assert_equal (insert 6 tree0) tree1;
    assert_equal (insert 3 tree1) tree2;
    assert_equal (insert 1 tree2) tree3;
    assert_equal (insert 4 tree3) tree4;
    assert_equal (insert 5 tree4) tree5; 
    assert_equal (insert 10 tree5) tree6; 
    assert_equal (insert 7 tree6) tree7;
    assert_equal (insert 8 tree7) tree8;
    assert_equal (insert 9 tree8) tree9;
    assert_equal (insert 2 tree9) tree10;  
  );

]

let _ = run_test_tt_main all_tests

