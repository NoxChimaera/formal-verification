theory Lab2_Ex
imports Main
begin

(* Topic: Recursion, induction and counterexamples *)

(* 
  replace :: Old \<Rightarrow> New \<Rightarrow> List \<Rightarrow> List'  
  Replaces all occurences of Old in List with New.
*)
primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "replace x y [] = []"
  | "replace x y (z#zs) = (if z = x then y else z)#(replace x y zs)"

value "replace 1 0 [1, 1, 2] :: int list"

(*
  del1 :: Item \<Rightarrow> List \<Rightarrow> List'
  Deletes first occurence of Item in List.
*)
primrec del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "del1 x [] = []"
  | "del1 x (y#ys) = (if y = x then ys else y#(del1 x ys))"

value "del1 1 [0, 0, 1, 1] :: int list"

(*
  delall :: Item \<Rightarrow> List \<Rightarrow> List'
  Deletes all occurences of Item in List.
*)
primrec delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "delall x [] = []"
  | "delall x (y#ys) = (if y = x then (delall x ys) else y#(delall x ys))"

value "delall 0 [1, 1, 0, 0, 1] :: int list"

(* Вариант 3: 3 и 5
    3: theorem "del1 x (del1 y zs) = del1 y (del1 x zs)"
    5: theorem "del1 y (replace x y xs) = del1 x xs"
*)

(* 
  prove 
  e.g.:
    List = [0, 0, 1, 2]
    del1 0 (del1 1 List) = del1 1 (del1 0 List) = [2]
*)
theorem [simp]: "del1 x (del1 y zs) = del1 y (del1 x zs)"
  apply(induct_tac zs)
  apply auto
done

(* 
  fail to prove 
  e.g.:
    List = [0, 0, 1, 1]
    LHS: del1 1 (replace 0 1 List) = [1, 1, 1]
    RHS: del1 0 List = [0, 1, 1]
    [1, 1, 1] \<noteq> [0, 1, 1]
*)
theorem "del1 y (replace x y xs) = del1 x xs"
  apply(induct_tac xs)
  apply auto
  quickcheck 1
  quickcheck 2
  quickcheck 3
oops