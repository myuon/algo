theory InsertionSort
  imports Main "HOL-Hoare.Separation"
begin

fun swapAt where
  "swapAt i j xs = list_update (list_update xs i (xs ! j)) j (xs ! i)"

lemma swapAt_same: "i < length xs \<Longrightarrow> swapAt i i xs = xs"
  apply (induct xs)
  apply simp
  apply simp
  done

lemma swapAt_nth: "\<And>k. i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> swapAt i j xs ! k = (if k = i then xs ! j else if k = j then xs ! i else xs ! k)"
  apply (induct xs)
  apply auto
  apply (metis list_update.simps(2) list_update_id)
  apply (metis length_Cons length_list_update list_update.simps(2) nth_list_update_eq)
  apply (metis length_Cons list_update.simps(2) nth_list_update_eq)
  by (metis list_update.simps(2) nth_list_update_neq)

inductive array where
  "array H p 0 []"
| "H p = Some a \<Longrightarrow> array H (p+1) k as \<Longrightarrow> array H p (Suc k) (a#as)"

lemma array_length:
  "array H p k xs \<Longrightarrow> length xs = k"
  apply (induct rule: array.induct)
  apply auto
  done

lemma array_singleton:
  assumes "array H p 1 xs"
  obtains x where "xs = [x]"
  using assms
  by (metis One_nat_def array.cases nat.simps(1) nat.simps(3))

lemma array_empty_from: "array H p n [] \<Longrightarrow> n = 0"
  apply (cases n)
  apply simp
  apply simp
  using array_length by force

lemma array_exists_under_heap_modification:
  assumes "array H p n xs"
  obtains zs where "array (H(x \<mapsto> y)) p n zs" "\<And>i. i < n \<Longrightarrow> if x = p + i then zs ! i = y else zs ! i = xs ! i"
proof-
  have "array H p n xs \<Longrightarrow> \<exists>zs. array (H(x \<mapsto> y)) p n zs \<and> (\<forall>i. i < n \<longrightarrow> (if x = p + i then zs ! i = y else zs ! i = xs ! i))"
    apply (induct rule: array.induct)
    using array.intros(1) apply blast
  proof-
    fix H p a k as
    assume "H p = Some a" "array H (p + 1) k as"
    and "\<exists>zs. array (H(x \<mapsto> y)) (p + 1) k zs \<and> (\<forall>i<k. if x = p + 1 + i then zs ! i = y else zs ! i = as ! i)"
    obtain zs where "array (H(x \<mapsto> y)) (p + 1) k zs \<and> (\<forall>i<k. if x = p + 1 + i then zs ! i = y else zs ! i = as ! i)"
      using \<open>\<exists>zs. array (H(x \<mapsto> y)) (p + 1) k zs \<and> (\<forall>i<k. if x = p + 1 + i then zs ! i = y else zs ! i = as ! i)\<close> by blast
    have "length zs = k"
      using \<open>array (H(x \<mapsto> y)) (p + 1) k zs \<and> (\<forall>i<k. if x = p + 1 + i then zs ! i = y else zs ! i = as ! i)\<close> array_length by blast

    { assume "p = x"
      have "\<And>i. i < k \<Longrightarrow> x \<noteq> p + 1 + i"
        by (simp add: \<open>p = x\<close>)
      hence "\<And>i. i < k \<Longrightarrow> zs ! i = as ! i"
        by (simp add: \<open>array (H(x \<mapsto> y)) (p + 1) k zs \<and> (\<forall>i<k. if x = p + 1 + i then zs ! i = y else zs ! i = as ! i)\<close>)
      hence "zs = as"
        by (metis \<open>array H (p + 1) k as\<close> \<open>length zs = k\<close> array_length list_eq_iff_nth_eq)

      have "array (H(x \<mapsto> y)) p (Suc k) (y # zs) \<and> (\<forall>i<Suc k. if x = p + i then (y # zs) ! i = y else (y # zs) ! i = (a # as) ! i)"
        by (metis \<open>array (H(x \<mapsto> y)) (p + 1) k zs \<and> (\<forall>i<k. if x = p + 1 + i then zs ! i = y else zs ! i = as ! i)\<close> \<open>p = x\<close> \<open>zs = as\<close> add.right_neutral add_left_cancel array.intros(2) fun_upd_same nth_Cons')
    }
    hence "p = x \<Longrightarrow> array (H(x \<mapsto> y)) p (Suc k) (y # zs) \<and> (\<forall>i<Suc k. if x = p + i then (y # zs) ! i = y else (y # zs) ! i = (a # as) ! i)"
      by blast

    { assume "p \<noteq> x"

      have "array (H(x \<mapsto> y)) p (Suc k) (a # zs) \<and> (\<forall>i<Suc k. if x = p + i then (a # zs) ! i = y else (a # zs) ! i = (a # as) ! i)"
        by (smt \<open>H p = Some a\<close> \<open>array (H(x \<mapsto> y)) (p + 1) k zs \<and> (\<forall>i<k. if x = p + 1 + i then zs ! i = y else zs ! i = as ! i)\<close> \<open>p \<noteq> x\<close> add.right_neutral add_diff_cancel_left' array.intros(2) group_cancel.add1 less_Suc_eq_0_disj map_upd_Some_unfold nth_Cons_0 nth_Cons_pos plus_1_eq_Suc)
    }
    hence "p \<noteq> x \<Longrightarrow> array (H(x \<mapsto> y)) p (Suc k) (a # zs) \<and> (\<forall>i<Suc k. if x = p + i then (a # zs) ! i = y else (a # zs) ! i = (a # as) ! i)"
      by blast

    show "\<exists>zs. array (H(x \<mapsto> y)) p (Suc k) zs \<and> (\<forall>i<Suc k. if x = p + i then zs ! i = y else zs ! i = (a # as) ! i)"
      using \<open>p = x \<Longrightarrow> array (H(x \<mapsto> y)) p (Suc k) (y # zs) \<and> (\<forall>i<Suc k. if x = p + i then (y # zs) ! i = y else (y # zs) ! i = (a # as) ! i)\<close> \<open>p \<noteq> x \<Longrightarrow> array (H(x \<mapsto> y)) p (Suc k) (a # zs) \<and> (\<forall>i<Suc k. if x = p + i then (a # zs) ! i = y else (a # zs) ! i = (a # as) ! i)\<close> by blast
  qed

  show "(\<And>zs. array (H(x \<mapsto> y)) p n zs \<Longrightarrow> (\<And>i. i < n \<Longrightarrow> if x = p + i then zs ! i = y else zs ! i = xs ! i) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    using assms
    using \<open>array H p n xs \<Longrightarrow> \<exists>zs. array (H(x \<mapsto> y)) p n zs \<and> (\<forall>i<n. if x = p + i then zs ! i = y else zs ! i = xs ! i)\<close> by blast
qed

lemma array_list_at:
  "array H p n xs \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> Some (xs ! k) = H (p + k))"
  apply (induct rule: array.induct)
  apply auto
  using less_Suc_eq_0_disj by auto

lemma array_swap_at:
  assumes "array H p n xs" "i < length xs" "j < length xs"
  shows "array (H(p + i \<mapsto> the (H (p + j)), p + j \<mapsto> the (H (p + i)))) p n (swapAt i j xs)"
proof-
  obtain ys where
    ys_array: "array (H(p + i \<mapsto> the (H (p + j)))) p n ys"
    and "\<And>k. k < n \<Longrightarrow> if p + i = p + k then ys ! k = the (H (p + j)) else ys ! k = xs ! k"
    apply (rule array_exists_under_heap_modification [OF assms(1), of "p + i" "the (H (p + j))"])
    by blast
  obtain zs where
    "array (H(p + i \<mapsto> the (H (p + j)), p + j \<mapsto> the (H (p + i)))) p n zs"
    "\<And>k. k < n \<Longrightarrow> if p + j = p + k then zs ! k = the (H (p + i)) else zs ! k = ys ! k"
    apply (rule array_exists_under_heap_modification [OF ys_array, of "p + j" "the (H (p + i))"])
    by blast

  have "\<And>k. k < n \<Longrightarrow> if k = i then zs ! k = the (H (p + j)) else if k = j then zs ! k = the (H (p + i)) else zs ! k = xs ! k"
    by (simp add: \<open>\<And>k. k < n \<Longrightarrow> if p + i = p + k then ys ! k = the (H (p + j)) else ys ! k = xs ! k\<close> \<open>\<And>k. k < n \<Longrightarrow> if p + j = p + k then zs ! k = the (H (p + i)) else zs ! k = ys ! k\<close>)
  have "xs ! j = the (H (p + j))" "xs ! i = the (H (p + i))"
    apply (metis array_length array_list_at assms(1) assms(3) option.sel)
    by (metis array_length array_list_at assms(1) assms(2) option.sel)
  have "\<And>k. k < n \<Longrightarrow> zs ! k = (if k = i then xs ! j else if k = j then xs ! i else xs ! k)"
    by (simp add: \<open>\<And>k. k < n \<Longrightarrow> if k = i then zs ! k = the (H (p + j)) else if k = j then zs ! k = the (H (p + i)) else zs ! k = xs ! k\<close> \<open>xs ! i = the (H (p + i))\<close> \<open>xs ! j = the (H (p + j))\<close>)
  have "\<And>k. k < n \<Longrightarrow> swapAt i j xs ! k = (if k = i then xs ! j else if k = j then xs ! i else xs ! k)"
    using assms(2) assms(3) swapAt_nth by blast
  have "\<And>k. k < n \<Longrightarrow> zs ! k = swapAt i j xs ! k"
    using \<open>\<And>k. k < n \<Longrightarrow> swapAt i j xs ! k = (if k = i then xs ! j else if k = j then xs ! i else xs ! k)\<close> \<open>\<And>k. k < n \<Longrightarrow> zs ! k = (if k = i then xs ! j else if k = j then xs ! i else xs ! k)\<close> by auto
  have "length zs = n"
    using \<open>array (H(p + i \<mapsto> the (H (p + j)), p + j \<mapsto> the (H (p + i)))) p n zs\<close> array_length by blast
  have "zs = swapAt i j xs"
    by (metis \<open>\<And>k. k < n \<Longrightarrow> zs ! k = swapAt i j xs ! k\<close> \<open>length zs = n\<close> array_length assms(1) length_list_update list_eq_iff_nth_eq swapAt.simps)

  show ?thesis
    using \<open>array (H(p + i \<mapsto> the (H (p + j)), p + j \<mapsto> the (H (p + i)))) p n zs\<close> \<open>zs = swapAt i j xs\<close> by blast
qed

primrec count where
  "count a [] = 0"
| "count a (x#xs) = (if a = x then Suc (count a xs) else count a xs)"

definition permute where
  "permute xs ys \<equiv> (\<forall>a. count a xs = count a ys)"

primrec head_swap_with where
  "head_swap_with [] y = [y]"
| "head_swap_with (x#xs) y = x#y#xs"

fun removeAt where
  "removeAt i xs = take (i-1) xs @ drop (i+1) xs"

lemma "
  VARS H i j tmp
  {array H arr N xs}
  i := 1;
  WHILE i < N
  INV {\<exists>zs. array H arr (i - 1) zs \<and> sorted zs} DO
    j := i;
    WHILE j > 0 & the (H (arr + j - 1)) > the (H (arr + j))
    INV {\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')} DO
      tmp := the (H (arr + j));
      H := H (arr + j \<mapsto> the (H (arr + j - 1)));
      H := H (arr + j - 1 \<mapsto> tmp);
      j := j - 1
    OD;
    i := i + 1
  OD
  {array H arr N ys \<and> sorted ys \<and> permute xs ys}
"
  apply vcg
proof-
  show "\<And>H i j tmp. array H arr N xs \<Longrightarrow> \<exists>zs. array H arr (1 - 1) zs \<and> sorted zs"
    apply simp
    using array.intros(1) sorted.simps(1) by blast
  show "\<And>H i j tmp. (\<exists>zs. array H arr (i - 1) zs \<and> sorted zs) \<and> i < N \<Longrightarrow> \<exists>zs'. i \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt i zs')"
    sorry

  show "\<And>H i j tmp.
       (\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1)) \<Longrightarrow>
       \<exists>zs'. j - 1 \<le> i \<and> array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) arr (i - 1) zs' \<and> sorted (removeAt (j - 1) zs')"
  proof-
    fix H i j tmp
    assume "(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))"
    obtain zs' where "j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')"
      using \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> by blast
    have "j - 1 \<le> i"
      using \<open>j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')\<close> le_diff_conv trans_le_add1 by blast
    define zs where "zs \<equiv> swapAt j (j - 1) zs'"
    have "array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) arr (i - 1) zs"
      apply (simp add: zs_def)

    show "\<exists>zs'. j - 1 \<le> i \<and> array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) arr (i - 1) zs' \<and> sorted (removeAt (j - 1) zs')"

  show "\<And>H i j tmp.
       (\<exists>k zs1 zs2.
           k < j \<and>
           j \<le> i \<and>
           array H arr k zs1 \<and>
           the (H (arr + k)) \<le> Min (set zs1) \<and> array H (arr + k) (i - k) zs2 \<and> Min (set (removeAt (j - k) zs2)) \<le> the (H (arr + k))) \<and>
       0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1)) \<Longrightarrow>
       \<exists>k zs1 zs2.
          k < j - 1 \<and>
          j - 1 \<le> i \<and>
          array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) arr k zs1 \<and>
          the ((H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) (arr + k)) \<le> Min (set zs1) \<and>
          array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) (arr + k) (i - k) zs2 \<and>
          Min (set (removeAt (j - 1 - k) zs2)) \<le> the ((H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) (arr + k))"
  proof-
    fix H i j tmp
    assume "(\<exists>k zs1 zs2.
           k < j \<and>
           j \<le> i \<and>
           array H arr k zs1 \<and>
           the (H (arr + k)) \<le> Min (set zs1) \<and> array H (arr + k) (i - k) zs2 \<and> Min (set (removeAt (j - k) zs2)) \<le> the (H (arr + k))) \<and>
       0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))"
    obtain k zs1 zs2 where "k < j \<and>
           j \<le> i \<and>
           array H arr k zs1 \<and>
           the (H (arr + k)) \<le> Min (set zs1) \<and> array H (arr + k) (i - k) zs2 \<and> Min (set (removeAt (j - k) zs2)) \<le> the (H (arr + k))"
      using \<open>(\<exists>k zs1 zs2. k < j \<and> j \<le> i \<and> array H arr k zs1 \<and> the (H (arr + k)) \<le> Min (set zs1) \<and> array H (arr + k) (i - k) zs2 \<and> Min (set (removeAt (j - k) zs2)) \<le> the (H (arr + k))) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> by blast
    have "k = j - 1 \<Longrightarrow> False"
    proof-
      assume "k = j - 1"
      have ""

    show "\<exists>k zs1 zs2.
          k < j - 1 \<and>
          j - 1 \<le> i \<and>
          array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) arr k zs1 \<and>
          the ((H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) (arr + k)) \<le> Min (set zs1) \<and>
          array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) (arr + k) (i - k) zs2 \<and>
          Min (set (removeAt (j - 1 - k) zs2)) \<le> the ((H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) (arr + k))"

  show "\<And>H i j tmp.
       (\<exists>zs'. 0 < j \<and> j \<le> i \<and> array H (arr + j) (i - j) zs' \<and> sorted zs') \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1)) \<Longrightarrow>
       \<exists>zs'. 0 < j - 1 \<and>
             j - 1 \<le> i \<and> array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) (arr + (j - 1)) (i - (j - 1)) zs' \<and> sorted zs'"
  proof-
    fix H and i j tmp
    assume "(\<exists>zs'. 0 < j \<and> j \<le> i \<and> array H (arr + j) (i - j) zs' \<and> sorted zs') \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))"
    obtain zs where "0 < j \<and> j \<le> i \<and> array H (arr + j) (i - j) zs \<and> sorted zs"
      using \<open>(\<exists>zs'. 0 < j \<and> j \<le> i \<and> array H (arr + j) (i - j) zs' \<and> sorted zs') \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> by blast
    define zs' where "zs' \<equiv> head_swap_with zs (the (H (arr + j - 1)))"

    have "array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) (arr + j - 1) (i - (j - 1)) zs'"
      apply (simp add: zs'_def)
      apply (cases zs)
    proof-
      assume "zs = []"
      have "i = j"
        using \<open>0 < j \<and> j \<le> i \<and> array H (arr + j) (i - j) zs \<and> sorted zs\<close> \<open>zs = []\<close> array_empty_from diff_is_0_eq le_antisym by blast
      hence h: "i - (j - Suc 0) = 1"
        by (simp add: Suc_leI \<open>(\<exists>zs'. 0 < j \<and> j \<le> i \<and> array H (arr + j) (i - j) zs' \<and> sorted zs') \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close>)

      have h2: "head_swap_with zs (the (H (arr + j - Suc 0))) = [the (H (arr + j - Suc 0))]"
        by (simp add: \<open>zs = []\<close>)

      show "array (H(arr + j \<mapsto> the (H (arr + j - Suc 0)), arr + j - Suc 0 \<mapsto> the (H (arr + j)))) (arr + j - Suc 0) (i - (j - Suc 0)) 
        (head_swap_with zs (the (H (arr + j - Suc 0))))"
        apply (simp add: h h2)
        apply rule
        apply (simp add: Suc_leI \<open>(\<exists>zs'. 0 < j \<and> j \<le> i \<and> array H (arr + j) (i - j) zs' \<and> sorted zs') \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close>)
        apply rule
        done
    next
      fix a as
      assume "zs = a # as"
      have h: "head_swap_with zs (the (H (arr + j - Suc 0))) = a # the (H (arr + j - Suc 0)) # as"
        by (simp add: \<open>zs = a # as\<close>)
      have a: "a = the (H (arr + j))"
        by (metis \<open>0 < j \<and> j \<le> i \<and> array H (arr + j) (i - j) zs \<and> sorted zs\<close> \<open>zs = a # as\<close> array.cases list.discI nth_Cons_0 option.sel)

      have "array H (arr + j + 1) (i - j - 1) as"
        by (metis One_nat_def \<open>0 < j \<and> j \<le> i \<and> array H (arr + j) (i - j) zs \<and> sorted zs\<close> \<open>zs = a # as\<close> add_diff_cancel_right' add_is_0 array.cases array_length list.inject list.size(4) nat.simps(3))

      have "i - j \<ge> 1"
        using \<open>0 < j \<and> j \<le> i \<and> array H (arr + j) (i - j) zs \<and> sorted zs\<close> \<open>zs = a # as\<close> array_length by fastforce
      obtain k where k: "i - (j - Suc 0) = Suc (Suc k)"
        using Suc_diff_le \<open>(\<exists>zs'. 0 < j \<and> j \<le> i \<and> array H (arr + j) (i - j) zs' \<and> sorted zs') \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>1 \<le> i - j\<close> diff_Suc_1 by fastforce

      show "array (H(arr + j \<mapsto> the (H (arr + j - Suc 0)), arr + j - Suc 0 \<mapsto> the (H (arr + j)))) (arr + j) (i - (j - Suc 0))
        (head_swap_with zs (the (H (arr + j - Suc 0))))"
        apply (simp add: h k)
        apply rule
        apply (simp add: a)

    show "\<exists>zs'. j - 1 \<le> i \<and> array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) (arr + (j - 1)) (i - (j - 1)) zs' \<and> sorted zs'"

end
