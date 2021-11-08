open Assert

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

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

let dp_product_test = [ "hw5programs/dp_product_except_self.oat", "",
                 "[0,0,9,0,0]\n[24,12,8,6] 0" ]

let sll_test = [ "hw5programs/reverse_sll.oat", "",
                 "The value of the first node of the reversed list is: 5" ]

let provided_tests : suite = let open Gradedtests in [
  Test("array index/length unit tests", linda_unit_tests);
  Test("reverse singly-linked list", executed_oat_file sll_test);
  Test("dp product except self", executed_oat_file dp_product_test);
] 


(* reverse SLL: https://leetcode.com/problems/reverse-linked-list/

    def reverseList(self, head: Optional[ListNode]) -> Optional[ListNode]:
        prev = None
        while head is not None:
            curr = head
            head = head.next
            curr.next = prev
            prev = curr
        return prev

*)

(* product except self: https://leetcode.com/problems/product-of-array-except-self/

       def productExceptSelf(self, nums: List[int]) -> List[int]:
        nums_len = len(nums)
        prefix = [1]
        suffix = [1] * nums_len
        res = []
        for i in range(1, nums_len):
            j = nums_len - i - 1
            prefix.append(prefix[i-1] * nums[i-1])
            suffix[j] = suffix[j+1] * nums[j+1]
        for k in range(0, nums_len):
            res.append(prefix[k] * suffix[k])
        return res

*)
