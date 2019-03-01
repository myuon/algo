theory SelectionSort
  imports Main MVector
begin

lemma take_induct:
  assumes "P []"
  and "\<And>i. \<lbrakk> P (take i xs); i < size xs \<rbrakk> \<Longrightarrow> P (take (i+1) xs)"
  shows "P xs"
proof-
  have "\<And>(n :: nat). n < size xs \<Longrightarrow> P (take n xs)"
  proof-
    fix n
    assume "n < size xs"
    show "P (take n xs)"
      apply (induct n)
      apply (simp add: assms(1))
      using assms(2) by fastforce
  qed
  thus ?thesis
    by (metis Suc_eq_plus1 assms(1) assms(2) gr0_conv_Suc leI lessI order_refl take0 take_all)
qed

lemma forM_invariant:
  assumes "P 0 ((),h)"
  and "\<And>i h. \<lbrakk> P i (execute (forMu (take i xs) program) h); i < size xs \<rbrakk> \<Longrightarrow> P (i+1) (execute (forMu (take (i+1) xs) program) h)"
  shows "P (size xs) (execute (forMu xs program) h)"
  apply (induct xs rule: take_induct)
  apply (simp add: return_def assms(1))
  apply (metis Suc_eq_plus1 Suc_leI assms(2) length_take min.absorb2 nat_less_le)
  done

definition selection_sort :: "nat mvector \<Rightarrow> unit io" where
  "selection_sort arr = (let n = size_of_mvector arr in forMu [0..<n] (\<lambda>i. do {
    min_ref \<leftarrow> ref i;
    forMu [i..<n] (\<lambda>j. do {
      valJ \<leftarrow> read arr (j+1);
      m \<leftarrow> ! min_ref;
      valMin \<leftarrow> read arr m;
      whenu (valJ < valMin) (min_ref := j)
    });
    m \<leftarrow> ! min_ref;
    swap arr i m;
    return ()
  }))"

primrec sorted :: "'a::ord list \<Rightarrow> bool" where
  "sorted [] = True"
| "sorted (x#xs) = ((\<forall>y\<in>set xs. x \<le> y) \<and> sorted xs)"

fun selection_sort_program where
  "selection_sort_program xs = do {
    arr \<leftarrow> from_list xs;
    selection_sort arr;
    to_list arr
  }"

definition outer_loop where
  "outer_loop arr n i = (do {
    min_ref \<leftarrow> ref i;
    forMu [i..<n] (\<lambda>j. do {
      valJ \<leftarrow> read arr (j+1);
      m \<leftarrow> ! min_ref;
      valMin \<leftarrow> read arr m;
      whenu (valJ < valMin) (min_ref := j)
    });
    m \<leftarrow> ! min_ref;
    swap arr i m;
    return ()
  })"

lemma selection_sort_as_outer_loop: "selection_sort arr = (let n = size_of_mvector arr in forMu [0..<n] (outer_loop arr n))"
  unfolding selection_sort_def outer_loop_def
  by simp

definition is_sorted_outer where
  "is_sorted_outer mvec i n h = (case execute (forMu [0..<i] (outer_loop mvec n)) h of (_,h') \<Rightarrow> sorted (take i (get_over mvec h')))"

lemma outer_loop_invariant:
  assumes "n = size_of_mvector arr"
  and "\<And>i. \<lbrakk> is_sorted_outer arr i n h; i < n \<rbrakk> \<Longrightarrow> is_sorted_outer arr (i+1) n h"
  shows "is_sorted_outer arr n n h"
  apply (simp add: is_sorted_outer_def)
  using forM_invariant [of "\<lambda>i _. is_sorted_outer arr i n h"]
  by (metis (mono_tags, lifting) SelectionSort.sorted.simps(1) assms(2) diff_zero is_sorted_outer_def length_upt split_def take0)

lemma outer_loop_step:
  assumes "is_sorted_outer arr i (size xs) h" "i < size xs"
  shows "is_sorted_outer arr (i+1) (size xs) h"
proof-
  have "case execute (forMu [0..<i] (outer_loop arr (size xs))) h of (_,h') \<Rightarrow> sorted (take i (get_over arr h'))"
    using assms (1)
    apply (simp add: is_sorted_outer_def)
    done

  have "\<And>h'. sorted (take i (get_over arr h')) \<Longrightarrow> case execute (outer_loop arr (size xs) i) h' of (_,h'') \<Rightarrow> sorted (take (i+1) (get_over arr h''))"
    sorry

  hence "case execute (do {
    forMu [0..<i] (outer_loop arr (size xs));
    outer_loop arr (size xs) i
  }) h of (_,h') \<Rightarrow> sorted (take (i+1) (get_over arr h'))"
    apply (simp add: execute_bind)
    using \<open>case execute (forMu [0..<i] (outer_loop arr (size xs))) h of (x, h') \<Rightarrow> SelectionSort.sorted (take i (get_over arr h'))\<close> by fastforce
  thus "is_sorted_outer arr (i+1) (size xs) h"
    apply (simp add: is_sorted_outer_def forMu_app)
    done
qed

theorem selection_sort_is_sorted:
  assumes "effect (selection_sort_program xs) h h' rs"
  shows "sorted rs"
proof-
  obtain h' arr where
    "effect (from_list xs) h h' arr"
    "size_of_mvector arr = size xs"
    by (simp add: effect_def execute_from_list get_over_def alloc_def)
  hence X: "execute (from_list xs) h = (arr,h')"
    by (simp add: effect_def)
  
  have "\<And>h. size (get_over arr h) = size xs"
    apply (simp add: get_over_def get_over_internal_def)
    by (metis \<open>size_of_mvector arr = length xs\<close>)
  hence "\<And>h. take (size xs) (get_over arr h) = get_over arr h"
    by simp

  have "\<And>i. \<lbrakk> is_sorted_outer arr i (size xs) h'; i < size xs \<rbrakk> \<Longrightarrow> is_sorted_outer arr (i+1) (size xs) h'"
    sorry
  hence "is_sorted_outer arr (size xs) (size xs) h'"
    by (simp add: \<open>size_of_mvector arr = length xs\<close> outer_loop_invariant)
  hence "is_sorted_outer arr (size xs) (size xs) h'"
    by simp
  hence "(case execute (selection_sort arr) h' of (_,h') \<Rightarrow> sorted (take (size xs) (get_over arr h')))"
    apply (simp add: is_sorted_outer_def selection_sort_as_outer_loop)
    by (metis \<open>size_of_mvector arr = length xs\<close>)
  hence "(case execute (selection_sort arr) h' of (_,h') \<Rightarrow> sorted (get_over arr h'))"
    by (simp add: \<open>\<And>h. take (length xs) (get_over arr h) = get_over arr h\<close>)
  hence Y: "case execute (do { selection_sort arr; to_list arr }) h' of (rs,_) \<Rightarrow> sorted rs"
    by (simp add: execute_bind execute_to_list, auto)

  have "case execute (selection_sort_program xs) h of (rs,_) \<Rightarrow> sorted rs"
    using Y
    apply (simp add: execute_bind X)
    done
  thus ?thesis
    using assms
    apply (simp add: effect_def)
    done
qed

definition inner_loop where
  "inner_loop arr n i min_ref j = (do {
    valJ \<leftarrow> read arr (j+1);
    m \<leftarrow> ! min_ref;
    valMin \<leftarrow> read arr m;
    whenu (valJ < valMin) (min_ref := j)
  })"

lemma outer_loop_as_inner_loop: "outer_loop arr n i = (do {
  min_ref \<leftarrow> ref i;
  forMu [i..<n] (inner_loop arr n i min_ref);
  m \<leftarrow> ! min_ref;
  swap arr i m;
  return ()
})"
  unfolding outer_loop_def inner_loop_def
  by simp

definition inner_inv where
  "inner_inv arr n i min_ref j h = (\<forall>k. i \<le> k \<and> k \<le> j \<longrightarrow> IO.get h min_ref \<le> MVector.get_at h arr k)"

lemma inner_loop_invariant:
  assumes "n = size_of_mvector arr"
  and "\<And>j. \<lbrakk> inner_inv arr n i min_ref j h; j < n \<rbrakk> \<Longrightarrow> inner_inv arr n i min_ref (j+1) h"
  shows "inner_inv arr n i min_ref n h"
  using forM_invariant [of _ h "[i..<n]"]
  sorry

end
