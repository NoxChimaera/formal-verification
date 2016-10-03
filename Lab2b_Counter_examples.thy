theory Lab2b_Counter_examples
imports Main
begin

lemma "hd (xs @ ys) = hd xs"
  apply(induct_tac xs)
  apply auto
  nitpick
oops

value "hd ([] @ [a1])"

lemma "hd (xs @ ys) = hd xs"
  nitpick
oops

lemma "hd (xs @ ys) = hd xs"
  quickcheck
oops

end