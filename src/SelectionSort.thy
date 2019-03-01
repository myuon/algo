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
    forMu [i+1..<n] (\<lambda>j. do {
      valJ \<leftarrow> read arr j;
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
    forMu [i+1..<n] (\<lambda>j. do {
      valJ \<leftarrow> read arr j;
      m \<leftarrow> ! min_ref;
      valMin \<leftarrow> read arr m;
      whenu (valJ < valMin) (min_ref := j)
    });
    m \<leftarrow> ! min_ref;
    swap arr i m
  })"

lemma selection_sort_as_outer_loop: "selection_sort arr = (let n = size_of_mvector arr in forMu [0..<n] (outer_loop arr n))"
  unfolding selection_sort_def outer_loop_def
  by simp

definition outer_loop_find_min where
  "outer_loop_find_min arr n i = (do {
    min_ref \<leftarrow> ref i;
    forMu [i+1..<n] (\<lambda>j. do {
      valJ \<leftarrow> read arr j;
      m \<leftarrow> ! min_ref;
      valMin \<leftarrow> read arr m;
      whenu (valJ < valMin) (min_ref := j)
    });
    ! min_ref
  })"

lemma outer_loop_find_min_finds_min_index:
  assumes "effect (outer_loop_find_min arr n i) h h' r"
  shows "get_at h' arr r = Min (set (map (get_at h' arr) [i..<n]))"
  sorry

lemma outer_loop_as_find_min_and_swap:
  "outer_loop arr n i = outer_loop_find_min arr n i \<bind> (\<lambda>m. swap arr i m)"
  by (simp add: outer_loop_def outer_loop_find_min_def)

definition outer_loop_invariant where
  "outer_loop_invariant arr i n h = (\<exists>h'. effect (outer_loop arr n i) h h' () \<and> sorted (take i (get_over arr h')) \<and> get_at h' arr i = Min (set (map (get_at h' arr) [i+1..<n])))"

lemma outer_loop_invariant_step:
  assumes "outer_loop_invariant arr i n h"
  and "effect (outer_loop arr n i) h h' ()"
  shows "outer_loop_invariant arr (i+1) n h'"
proof-
  obtain h1 r where "effect (outer_loop_find_min arr n i) h h1 r" "effect (swap arr i r) h1 h' ()"
    by (metis assms(2) effect_bind outer_loop_as_find_min_and_swap)
  hence "get_at h1 arr r = Min (set (map (get_at h1 arr) [i..<n]))"
    using outer_loop_find_min_finds_min_index by blast
  hence "get_at h' arr i = Min (set (map (get_at h' arr) [i+1..<n]))"
    by (metis assms(1) assms(2) effectE outer_loop_invariant_def prod.sel(2))

  show ?thesis
    sorry
qed

definition inner_loop where
  "inner_loop arr n i min_ref j = (do {
    valJ \<leftarrow> read arr j;
    m \<leftarrow> ! min_ref;
    valMin \<leftarrow> read arr m;
    whenu (valJ < valMin) (min_ref := j)
  })"

lemma outer_loop_find_min_as_inner_loop:
  "outer_loop_find_min arr n i = (do {
    min_ref \<leftarrow> ref i;
    forMu [i+1..<n] (inner_loop arr n i min_ref);
    ! min_ref
  })"
  unfolding outer_loop_find_min_def inner_loop_def apply simp
  done

definition inner_loop_invariant where
  "inner_loop_invariant arr i n min_ref j h = (get_at h arr (IO.get h min_ref) = Min (set (map (get_at h arr) [i..<j])))"

(*
lemma execute_inner_loop: "execute (inner_loop arr n i min_ref j) h = ((), if get_at h arr (j+1) < get_at h arr (IO.get h min_ref) then IO.set min_ref j h else h)"
  apply (simp add: inner_loop_def)
  apply (simp add: execute_bind execute_read execute_lookup)
  apply (simp add: execute_update return_def)
  done
*)

lemma execute_if: "execute (if b then p else q) h = (if b then execute p h else execute q h)"
  by simp

lemma effect_inner_loop:
  fixes arr :: "nat mvector"
  assumes "effect (inner_loop arr i n min_ref j) h h' ()"
  shows "get_at h' arr (IO.get h' min_ref) = min (get_at h' arr (IO.get h min_ref)) (get_at h' arr j)"
  and "\<And>i. get_at h arr i = get_at h' arr i"
  using assms
  apply (simp add: effect_def inner_loop_def)
  apply (simp add: execute_bind execute_read execute_lookup)
  apply (simp add: execute_if)
  sorry
(*
proof-
  assume X: "(if get_at h arr j < get_at h arr (IO.get h min_ref) then execute (min_ref := j) h else execute (return ()) h) = ((), h')"

  { assume "get_at h arr j < get_at h arr (IO.get h min_ref)"
    hence "((), h') = execute (min_ref := j) h"
      using X by simp
    hence "h' = IO.set min_ref j h"
      by (simp add: execute_update)
    hence "get_at h' arr (IO.get h' min_ref) = min (get_at h' arr (IO.get h min_ref)) (get_at h' arr j)"
      apply simp

  }
  hence p: "get_at h arr j < get_at h arr (IO.get h min_ref) \<Longrightarrow> get_at h' arr (IO.get h' min_ref) = min (get_at h' arr (IO.get h' min_ref)) (get_at h' arr j)"
    by simp

  { assume "\<not> (get_at h arr j < get_at h arr (IO.get h min_ref))"
    hence "((), h') = execute (return ()) h"
      using X by auto
    hence "h' = h"
      using forMu_nil by auto
  }
  hence q: "\<not> (get_at h arr j < get_at h arr (IO.get h min_ref)) \<Longrightarrow> get_at h' arr (IO.get h' min_ref) = min (get_at h arr (IO.get h min_ref)) (get_at h arr j)"
    by simp

  show "get_at h' arr (IO.get h' min_ref) = min (get_at h' arr (IO.get h min_ref)) (get_at h' arr j)"
    using p q by auto
qed
*)

lemma inner_loop_invariant_step:
  fixes arr :: "nat mvector"
  assumes "inner_loop_invariant arr i n min_ref j h"
  and "effect (inner_loop arr i n min_ref j) h h' ()"
  and "i < j"
  shows "inner_loop_invariant arr i n min_ref (j+1) h'"
proof-
  have "get_at h arr (IO.get h min_ref) = Min (set (map (get_at h arr) [i..<j]))"
    by (meson assms(1) inner_loop_invariant_def)
  have "get_at h' arr (IO.get h' min_ref) = min (get_at h arr (IO.get h min_ref)) (get_at h arr j)"
    using assms(2) effect_inner_loop(1) effect_inner_loop(2) by fastforce
  also have "\<dots> = min (Min (set (map (get_at h arr) [i..<j]))) (get_at h arr j)"
    by (simp add: \<open>get_at h arr (IO.get h min_ref) = Min (set (map (get_at h arr) [i..<j]))\<close>)
  also have "\<dots> = Min (set (get_at h arr j # map (get_at h arr) [i..<j]))"
  proof-
    { fix f :: "nat \<Rightarrow> nat" and xs and x
      have "xs \<noteq> [] \<Longrightarrow> min (Min (set (map f xs))) (f x) = Min (set (f x # map f xs))"
        apply (induct xs arbitrary: x)
        apply auto
        done
    }
    have "\<And>(f :: nat \<Rightarrow> nat) xs j. xs \<noteq> [] \<Longrightarrow> min (Min (set (map f xs))) (f j) = Min (set (f j # map f xs))"
      by simp
    thus ?thesis
      by (simp add: assms(3))
  qed
  also have "\<dots> = Min (set (map (get_at h arr) [i..<j] @ [get_at h arr j]))"
    by auto
  also have "\<dots> = Min (set (map (get_at h arr) ([i..<j] @ [j])))"
    by auto
  also have "\<dots> = Min (set (map (get_at h arr) [i..<j+1]))"
    using assms(3) by auto
  also have "\<dots> = Min (set (map (get_at h' arr) [i..<j+1]))"
    by (metis assms(2) effect_inner_loop(2) map_cong)
  finally have "get_at h' arr (IO.get h' min_ref) = Min (set (map (get_at h' arr) [i..<j+1]))"
    by auto
  thus ?thesis
    unfolding inner_loop_invariant_def
    by simp
qed

(*
lemma outer_loop_invariant:
  assumes "n = size (get_over arr h)"
  and "\<And>i. \<lbrakk> is_sorted_outer arr i n h; i < n \<rbrakk> \<Longrightarrow> is_sorted_outer arr (i+1) n h"
  shows "is_sorted_outer arr n n h"
  using forM_invariant [of "\<lambda>i _. is_sorted_outer arr i n h" h "get_over arr h"]
  using assms(1) assms(2) is_sorted_outer_def by blast

lemma outer_loop_step:
  assumes "is_sorted_outer arr i (size xs) h" "i < size xs"
  shows "is_sorted_outer arr (i+1) (size xs) h"
proof-
  have "case execute (forMu [0..<i] (outer_loop arr (size xs))) h of (_,h') \<Rightarrow> sorted (take i (get_over arr h'))"
    using assms (1)
    apply (simp add: is_sorted_outer_def)
    apply auto
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
     (metis \<open>size_of_mvector arr = length xs\<close>)
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

lemma outer_loop_sorted:
  assumes "sorted (take i (get_over arr h'))"
  shows "case execute (outer_loop arr (size xs) i) h' of (_,h'') \<Rightarrow> sorted (take (i+1) (get_over arr h''))"
proof-
  have ""

lemma inner_loop_invariant:
  assumes "n = size_of_mvector arr"
  and "\<And>j. \<lbrakk> inner_inv arr n i min_ref j h; j < n \<rbrakk> \<Longrightarrow> inner_inv arr n i min_ref (j+1) h"
  shows "inner_inv arr n i min_ref n h"
  using forM_invariant [of _ h "[i..<n]"]
  sorry
*)


end
