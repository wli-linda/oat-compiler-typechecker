open Assert
open Gradedtests
open Ast
open Tctxt

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

(*
let totodaniel_oat_test =
  [("hw5programs/bst_for_all.oat", "", "00")]
  
let own_oat_test =
  [("hw5programs/nick_rytis_deque.oat", "", "10 5 15 2 3 15 5 2 -1 -1 0 0")] 
  
let contains_test = ["hw5programs/contains_ll.oat", "", "ex_ll: 246\nex_ll contains 4: true\nex_ll contains 7: false\nex_ll after inserting 5: 2456\nex_ll after deleting 4: 2560"]

let bst_set_test = [
    ("hw5programs/bst_set.oat", "", "12 34 76 79 102 234 no no yes no yes yes 0")
  ]

let alu_leyli_test =
  [("hw5programs/Leyli-Alaukik.oat", "", "3")]

let extra_given_test = [("hw5programs/for_scope.oat", "", "0")]

let hw5_sewen_test : suite = [ GradedTest ("sewen test", 0, executed_oat_file
                                             [("hw5programs/linkedlink_cmp.oat","", "0")])]

let gabriel_lim_li_test = [ "hw5programs/local_fn_reassignment.oat", "", "42" ]

let noel_praveen_tests = [
  (* NOTE: See brainf__k.sh for running the brainf*** interpreter standalone
   * and making sense of the return value, it is an ascii string.
   * The delimited output is in brainf__k.sh
   * also there's an extra '0' appended at the end of the output,
   * because it's the return value *)
  ("hw5programs/noel_praveen_brainf__k.oat",
   "\"255106++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++.000\"",
   "72101108108111328711111410810033100");
]

let ivan_mark_test = [ "hw5programs/red_black_tree.oat", "", "1" ]

let kevin_christian_oat_tests = [ ("hw5programs/hash_map.oat", "", "0") ] 


let emp = Tctxt.empty
let exp_1 = Ast.no_loc (Bop (Eq,Ast.no_loc (CInt 3L), Ast.no_loc (CInt 4L)) )
let s1 = Ast.no_loc (Ret (None))
let while_loop = Ast.no_loc (Ast.While (exp_1,[s1]))

let for_loop = Ast.no_loc (Ast.For([],Some exp_1,Some (s1),[s1]))
let nested_for_loop = Ast.no_loc (Ast.For([],Some exp_1,Some (s1),[for_loop]))
let super_nested_for_loop = Ast.no_loc (Ast.For([],Some exp_1,Some (s1),[nested_for_loop]))
let quite_nested_for_loop = Ast.no_loc (Ast.For([],Some exp_1,Some (s1),[super_nested_for_loop]))
*)

let linda_unit_tests =
  let open Ast in
  let arr_exp = no_loc @@ CArr (TInt, [no_loc @@ CInt 1L]) in
  let idx_exp = no_loc @@ CInt 0L in
  let idx_exp_bad = no_loc @@ CBool true in
  [ "array indexing ok index type", (fun () ->
        let _ = Typechecker.typecheck_exp Tctxt.empty
            (no_loc @@ Index (arr_exp, idx_exp)) in ()
      );
    "array indexing bad index type", (fun () ->
        try let _ = Typechecker.typecheck_exp Tctxt.empty
                (no_loc @@ Index (arr_exp, idx_exp_bad)) in
          failwith "Index not of type TInt"
        with Typechecker.TypeError _ -> ()
      );
    "array length ok exp type", (fun () ->
        let _ = Typechecker.typecheck_exp Tctxt.empty
            (no_loc @@ Length arr_exp) in ()
      );
    "array length bad exp type", (fun () ->
        try let _ = Typechecker.typecheck_exp Tctxt.empty
                (no_loc @@ Length idx_exp) in
          failwith "Length exp not an array"
        with Typechecker.TypeError _ -> ()
      );
  ]


(*


let github_unit_tests = [

"Typechecking For Statements",
  (fun () ->
     if snd (Typechecker.typecheck_stmt emp
               (for_loop) (RetVoid)) 
     then failwith "Should not return true" else ()
  );
  "Typechking Nested For Loops",
  (fun () ->
     if snd (Typechecker.typecheck_stmt emp
               (nested_for_loop) (RetVoid)) 
     then failwith "Should not return true" else ()
  );
  "Typechking thrice Nested For Loops",
  (fun () ->
     if snd (Typechecker.typecheck_stmt emp
               (super_nested_for_loop) (RetVoid)) 
     then failwith "Should not return true" else ()
  );
  "Typechking quadra Nested For Loops",
  (fun () ->
     if snd (Typechecker.typecheck_stmt emp
               (quite_nested_for_loop) (RetVoid)) 
     then failwith "Should not return true" else ()
  );

  
] *)

let provided_tests : suite = [
  (*
  Test("BST Test", executed_oat_file totodaniel_oat_test);
  Test ("Rytis and Nick's test - Deque", executed_oat_file own_oat_test); 
  Test("ll_contains", executed_oat_file contains_test);
  Test("BST set test", executed_oat_file bst_set_test);
  Test("leyli", executed_oat_file alu_leyli_test);
  Test("for_scope", executed_oat_file extra_given_test);
  Test("subtype unit tests", github_unit_tests); *) 
  Test("array index/length unit tests", linda_unit_tests); (*
  GradedTest ("sewen test", 0, executed_oat_file
                [("hw5programs/linkedlink_cmp.oat","", "0")]);
  GradedTest ("G and LL's test", 0, executed_oat_file gabriel_lim_li_test);
  GradedTest("noel praveen 3rd tests", 0, executed_oat_file noel_praveen_tests);
  Test ("Ivan Mark red black tree", Gradedtests.executed_oat_file ivan_mark_test);
  GradedTest ("kevin & christian oat tests", 0, executed_oat_file kevin_christian_oat_tests);
  GradedTest ("ivan and daniela test", 0, executed_oat_file
               [("hw5programs/swap_pairs.oat","", "1")]) *)
] 
