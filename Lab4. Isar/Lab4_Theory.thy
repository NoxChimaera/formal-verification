theory Lab4_Theory
imports Main
begin

(* Lecture *)
lemma "A \<and> B \<Longrightarrow> B \<and> A"
proof -
  assume ab: "A \<and> B"
  from ab have a: "A" by (rule conjunct1)
  from ab have b: "B" by (rule conjunct2)
  from b a show "B \<and> A" by (rule conjI)
qed

(* Lemma #1 *)
lemma "\<lbrakk>A; B\<rbrakk> \<Longrightarrow> A \<and> B"
proof -
 assume a: "A"
 assume b: "B"
 from a b show "A \<and> B" by (rule conjI)
qed

(* Lemma #2 *)
lemma "A \<Longrightarrow> A \<or> B"
proof -
  assume foo: "A"
  from foo show "A \<or> B" by (rule disjI1)
qed

(* Lemma #3 *)
lemma "\<lbrakk>A \<and> B; \<lbrakk>A; B\<rbrakk> \<Longrightarrow> C\<rbrakk> \<Longrightarrow> C"
proof -
  assume a: "A \<and> B"
  assume b: "\<lbrakk>A; B\<rbrakk> \<Longrightarrow> C"
  from a b show "C" by (rule conjE)
qed

(* Lemma #4 *)
lemma "\<lbrakk>(A \<Longrightarrow> B); (B \<Longrightarrow> A)\<rbrakk> \<Longrightarrow> A = B"
proof -
  assume fst: "A \<Longrightarrow> B"
  assume snd: "B \<Longrightarrow> A"
  from fst snd show "A = B" by (rule iffI)
qed

(* Lemma #6 *)
lemma "\<lbrakk>A \<or> B; (A \<Longrightarrow> C); (B \<Longrightarrow> C)\<rbrakk> \<Longrightarrow> C"
proof -
  assume fst: "A \<or> B"
  assume snd: "A \<Longrightarrow> C"
  assume trd: "B \<Longrightarrow> C"
  from fst snd trd show "C" by (rule disjE)
qed

(* Lemma #7 *)
lemma "\<lbrakk>A \<longrightarrow> B; A; (B \<Longrightarrow> C)\<rbrakk> \<Longrightarrow> C"
proof - 
  assume a: "A \<longrightarrow> B"
  assume b: "A"
  assume c: "B \<Longrightarrow> C"
  from a b c show "C" by (rule impE)
qed