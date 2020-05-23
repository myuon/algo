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
  "removeAt i xs = take i xs @ drop (i+1) xs"

lemma removeAt_length: "i < length xs \<Longrightarrow> length (removeAt i xs) = length xs - 1"
  apply (induct xs arbitrary: i)
  apply auto
  done

lemma removeAt_at: "\<And>k. i < length xs \<Longrightarrow> removeAt i xs ! k = (if k < i then xs ! k else xs ! (k + 1))"
  apply (induct xs arbitrary: i)
  apply auto
  apply (simp add: nth_append)
  by (simp add: min.absorb2 nth_append)

fun slice where
  "slice i j xs = drop (i - 1) (take j xs)"

lemma take_as_slice: "take n xs = slice 0 n xs"
  by simp

lemma sorted_for_slice: "sorted xs \<Longrightarrow> sorted (slice i j xs)"
  by (simp add: sorted_drop sorted_take)

lemma sorted_snoc:
  assumes "sorted xs" "\<And>k. k < length xs \<Longrightarrow> xs ! k \<le> z"
  shows "sorted (xs @ [z])"
proof-
  { fix n
    have "n = length xs \<and> sorted xs \<and> (\<forall>k. k < length xs \<longrightarrow> xs ! k \<le> z) \<Longrightarrow> sorted (xs @ [z])"
      apply (induct n arbitrary: xs)
      apply auto
    proof-
      fix n xs
      assume "(\<And>xs. n = length xs \<and> sorted xs \<and> (\<forall>k<length xs. xs ! k \<le> z) \<Longrightarrow> sorted (xs @ [z]))"
        "Suc n = length xs" "sorted xs" "\<forall>k<length xs. xs ! k \<le> z"
      obtain y ys where "xs = y # ys" "length ys = n"
        by (meson Suc_length_conv \<open>Suc n = length xs\<close>)
      have "sorted ys"
        using \<open>sorted xs\<close> \<open>xs = y # ys\<close> sorted.simps(2) by blast
      moreover have "\<forall>k < length ys. ys ! k \<le> z"
        using \<open>\<forall>k<length xs. xs ! k \<le> z\<close> \<open>xs = y # ys\<close> by auto
      ultimately have "sorted (ys @ [z])"
        by (simp add: \<open>\<And>xs. n = length xs \<and> sorted xs \<and> (\<forall>k<length xs. xs ! k \<le> z) \<Longrightarrow> sorted (xs @ [z])\<close> \<open>length ys = n\<close>)

      show "sorted (xs @ [z])"
        using \<open>\<forall>k<length xs. xs ! k \<le> z\<close> \<open>sorted (ys @ [z])\<close> \<open>sorted xs\<close> \<open>xs = y # ys\<close> list.discI by auto
    qed
  }
  hence "\<And>n. n = length xs \<and> sorted xs \<and> (\<forall>k. k < length xs \<longrightarrow> xs ! k \<le> z) \<Longrightarrow> sorted (xs @ [z])"
    by simp

  show ?thesis
    by (simp add: \<open>\<And>n. n = length xs \<and> sorted xs \<and> (\<forall>k<length xs. xs ! k \<le> z) \<Longrightarrow> sorted (xs @ [z])\<close> assms(1) assms(2))
qed

lemma sorted_concat:
  fixes xs :: "('a::linorder) list"
  assumes "sorted xs" "sorted ys" "\<And>k. k < length xs \<Longrightarrow> xs ! k \<le> z" "\<And>k. k < length ys \<Longrightarrow> z \<le> ys ! k"
  shows "sorted (xs @ [z] @ ys)"
proof-
  have "sorted (xs @ [z])"
    by (simp add: assms(1) assms(3) sorted_snoc)
  { fix n and xs :: "'a::linorder list" and ys :: "'a::linorder list"
    have "length ys = n \<Longrightarrow> sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> (\<And>k. ys \<noteq> [] \<Longrightarrow> k < length xs \<Longrightarrow> xs ! k \<le> ys ! 0) \<Longrightarrow> sorted (xs @ ys)"
      apply (induct n arbitrary: xs ys)
      apply simp
    proof-
      fix n and xs :: "'a::linorder list" and ys :: "'a::linorder list"
      assume hyp: "(\<And>(xs :: 'a::linorder list) ys. length ys = n \<Longrightarrow> sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> (\<And>k. ys \<noteq> [] \<Longrightarrow> k < length xs \<Longrightarrow> xs ! k \<le> ys ! 0) \<Longrightarrow> sorted (xs @ ys))"
        and "length ys = Suc n" "sorted xs" "sorted ys" "(\<And>k. ys \<noteq> [] \<Longrightarrow> k < length xs \<Longrightarrow> xs ! k \<le> ys ! 0)"
      obtain w and ws :: "'a::linorder list" where "ys = w # ws" "length ws = n"
        by (metis Suc_length_conv \<open>length ys = Suc n\<close>)
      have "sorted ws"
        using \<open>sorted ys\<close> \<open>ys = w # ws\<close> sorted.simps(2) by blast
      moreover have "sorted (xs @ [w])"
        using \<open>\<And>k. \<lbrakk>ys \<noteq> []; k < length xs\<rbrakk> \<Longrightarrow> xs ! k \<le> ys ! 0\<close> \<open>sorted xs\<close> \<open>ys = w # ws\<close> sorted_snoc by auto
      moreover have "\<And>k. ws \<noteq> [] \<Longrightarrow> k < length (xs @ [w]) \<Longrightarrow> (xs @ [w]) ! k \<le> ws ! 0"
        by (metis (no_types, hide_lams) \<open>\<And>k. \<lbrakk>ys \<noteq> []; k < length xs\<rbrakk> \<Longrightarrow> xs ! k \<le> ys ! 0\<close> \<open>sorted ys\<close> \<open>ys = w # ws\<close> dual_order.trans length_append_singleton less_Suc_eq list.distinct(1) list.exhaust nth_Cons_0 nth_append nth_append_length sorted2)
      ultimately show "sorted (xs @ ys)"
        using \<open>length ws = n\<close> \<open>ys = w # ws\<close> hyp by fastforce
    qed
  }
  thus ?thesis
    by (metis append_Cons append_Nil assms(1) assms(2) assms(3) assms(4) length_greater_0_conv nth_Cons_0 sorted.elims(2) sorted1 sorted2)
qed

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
  show "\<And>H i j tmp. (\<exists>zs. array H arr (i - 1) zs \<and> sorted zs) \<and> i < N \<Longrightarrow> (\<exists>zs'. i \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt i zs'))"
    sorry

  show "\<And>H i j tmp.
       ((\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs'))) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1)) \<Longrightarrow>
       (\<exists>zs'. j - 1 \<le> i \<and> array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) arr (i - 1) zs' \<and> sorted (removeAt (j - 1) zs'))"
  proof-
    fix H i j tmp
    assume "((\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs'))) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))"
    obtain xs where "j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)"
      using \<open>((\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs'))) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> by blast

    obtain ys where "array (H(arr + j \<mapsto> the (H (arr + j - 1)))) arr (i - 1) ys" "\<And>k. k < length ys \<Longrightarrow> ys ! k = (if arr + k = arr + j then the (H (arr + j - 1)) else xs ! k)"
      apply (rule array_exists_under_heap_modification [of "H" arr "i - 1" xs "arr + j" "the (H (arr + j - 1))"])
      using \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> apply blast
      by (simp add: array_length)
    obtain zs where "array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) arr (i - 1) zs" "\<And>k. k < length zs \<Longrightarrow> zs ! k = (if arr + k = arr + j - 1 then the (H (arr + j)) else ys ! k)"
      apply (rule array_exists_under_heap_modification [of "H(arr + j \<mapsto> the (H (arr + j - 1)))" arr "i - 1" ys "arr + j - 1" "the (H (arr + j))"])
      using \<open>array (H(arr + j \<mapsto> the (H (arr + j - 1)))) arr (i - 1) ys\<close> apply blast
      by (simp add: array_length)

    have "length zs = i - 1"
      using \<open>array (H(arr + j \<mapsto> the (H (arr + j - 1)), arr + j - 1 \<mapsto> the (H (arr + j)))) arr (i - 1) zs\<close> array_length by blast
    have "length ys = i - 1"
      using \<open>array (H(arr + j \<mapsto> the (H (arr + j - 1)))) arr (i - 1) ys\<close> array_length by blast

    have "\<And>k. k < length zs \<Longrightarrow> zs ! k = (if k = j - 1 then the (H (arr + j)) else if k = j then the (H (arr + j - 1)) else xs ! k)"
      by (metis (no_types, lifting) Nat.add_diff_assoc One_nat_def Suc_leI \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>\<And>k. k < length ys \<Longrightarrow> ys ! k = (if arr + k = arr + j then the (H (arr + j - 1)) else xs ! k)\<close> \<open>\<And>k. k < length zs \<Longrightarrow> zs ! k = (if arr + k = arr + j - 1 then the (H (arr + j)) else ys ! k)\<close> \<open>length ys = i - 1\<close> \<open>length zs = i - 1\<close> add_diff_cancel_left')

    have "sorted (removeAt j xs)"
      using \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> by blast

    { assume "j = i"
      have "\<And>k. k < i - 1 \<Longrightarrow> zs ! k = xs ! k"
        by (simp add: \<open>\<And>k. k < length zs \<Longrightarrow> zs ! k = (if k = j - 1 then the (H (arr + j)) else if k = j then the (H (arr + j - 1)) else xs ! k)\<close> \<open>j = i\<close> \<open>length zs = i - 1\<close> less_not_refl3)
      have "removeAt (i - 1) zs = removeAt (i - 1) xs"
        by (metis \<open>\<And>k. k < i - 1 \<Longrightarrow> zs ! k = xs ! k\<close> \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> \<open>length zs = i - 1\<close> array_length nth_equalityI)
      have "sorted (removeAt (i - 1) zs)"
        by (metis One_nat_def Suc_pred \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>j = i\<close> \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> \<open>removeAt (i - 1) zs = removeAt (i - 1) xs\<close> add.commute append_Nil2 array_length diff_le_self drop_all order_refl plus_1_eq_Suc removeAt.simps sorted_append take_all)
      have "sorted (removeAt (j - 1) zs)"
        using \<open>j = i\<close> \<open>sorted (removeAt (i - 1) zs)\<close> by blast
    }
    hence "j = i \<Longrightarrow> sorted (removeAt (j - 1) zs)"
      by blast

    { assume "j = i - 1"
      have "j - 1 < length zs"
        using \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>j = i - 1\<close> \<open>length zs = i - 1\<close> by linarith
      have "\<And>k. k < j - 1 \<Longrightarrow> zs ! k = xs ! k"
        using \<open>\<And>k. k < length zs \<Longrightarrow> zs ! k = (if k = j - 1 then the (H (arr + j)) else if k = j then the (H (arr + j - 1)) else xs ! k)\<close> \<open>j = i - 1\<close> \<open>length zs = i - 1\<close> by auto
      have "length zs = j"
        by (simp add: \<open>j = i - 1\<close> \<open>length zs = i - 1\<close>)
      have "length (removeAt (j - 1) zs) = j - 1"
        using \<open>j - 1 < length zs\<close> \<open>length zs = j\<close> removeAt_length by blast
      have "\<And>k. k < length (removeAt (j - 1) zs) \<Longrightarrow> removeAt (j - 1) zs ! k = removeAt (j - 1) xs ! k"
        by (metis \<open>\<And>k. k < j - 1 \<Longrightarrow> zs ! k = xs ! k\<close> \<open>j - 1 < length zs\<close> \<open>j = i - 1\<close> \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> \<open>length (removeAt (j - 1) zs) = j - 1\<close> \<open>length zs = j\<close> array_length removeAt_at)

      have "removeAt (j - 1) zs = removeAt (j - 1) xs"
        by (metis \<open>\<And>k. k < length (removeAt (j - 1) zs) \<Longrightarrow> removeAt (j - 1) zs ! k = removeAt (j - 1) xs ! k\<close> \<open>j - 1 < length zs\<close> \<open>j = i - 1\<close> \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> \<open>length zs = j\<close> array_length nth_equalityI removeAt_length)
      have "sorted (removeAt (j - 1) zs)"
        by (metis One_nat_def Suc_pred \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>j = i - 1\<close> \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> \<open>removeAt (j - 1) zs = removeAt (j - 1) xs\<close> add.commute append_Nil2 array_length drop_all order_refl plus_1_eq_Suc removeAt.simps sorted_append sorted_take take_all)
    }
    hence "j = i - 1 \<Longrightarrow> sorted (removeAt (j - 1) zs)"
      by blast

    { assume "j < i - 1"
      have "j < length zs"
        using \<open>j < i - 1\<close> \<open>length zs = i - 1\<close> by auto
      have "\<And>k. k < j - 1 \<Longrightarrow> zs ! k = xs ! k"
        using \<open>\<And>k. k < length zs \<Longrightarrow> zs ! k = (if k = j - 1 then the (H (arr + j)) else if k = j then the (H (arr + j - 1)) else xs ! k)\<close> \<open>j < i - 1\<close> \<open>length zs = i - 1\<close> by auto
      have "zs ! (j - 1) = the (H (arr + j))"
        by (simp add: \<open>\<And>k. k < length zs \<Longrightarrow> zs ! k = (if k = j - 1 then the (H (arr + j)) else if k = j then the (H (arr + j - 1)) else xs ! k)\<close> \<open>j < length zs\<close> less_imp_diff_less)
      have "zs ! j = the (H (arr + j - 1))"
        using \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>\<And>k. k < length zs \<Longrightarrow> zs ! k = (if k = j - 1 then the (H (arr + j)) else if k = j then the (H (arr + j - 1)) else xs ! k)\<close> \<open>j < length zs\<close> by auto

      have "xs ! (j - 1) = the (H (arr + j - 1))"
        by (metis (mono_tags, lifting) Nat.add_diff_assoc One_nat_def Suc_leI \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>j < length zs\<close> \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> \<open>length zs = i - 1\<close> array_list_at less_imp_diff_less option.sel)
      have "\<And>k. k < j - 1 \<Longrightarrow> (removeAt j xs) ! k \<le> (removeAt j xs) ! (j - 1)"
        by (metis One_nat_def Suc_leI \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>j < i - 1\<close> \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> array_length diff_less_mono less_imp_le_nat removeAt_length sorted_nth_mono)
      have "\<And>k. k < j - 1 \<Longrightarrow> (removeAt j xs) ! k = xs ! k \<and> (removeAt j xs) ! (j - 1) = xs ! (j - 1)"
        by (metis One_nat_def Suc_pred \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>j < i - 1\<close> \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> array_length less_Suc_eq removeAt_at)
      have "\<And>k. k < j - 1 \<Longrightarrow> xs ! k \<le> xs ! (j - 1)"
        using \<open>\<And>k. k < j - 1 \<Longrightarrow> removeAt j xs ! k = xs ! k \<and> removeAt j xs ! (j - 1) = xs ! (j - 1)\<close> \<open>\<And>k. k < j - 1 \<Longrightarrow> removeAt j xs ! k \<le> removeAt j xs ! (j - 1)\<close> by auto
      have "\<And>k. k < j - 1 \<Longrightarrow> zs ! k \<le> zs ! j"
        using \<open>\<And>k. k < j - 1 \<Longrightarrow> xs ! k \<le> xs ! (j - 1)\<close> \<open>\<And>k. k < j - 1 \<Longrightarrow> zs ! k = xs ! k\<close> \<open>xs ! (j - 1) = the (H (arr + j - 1))\<close> \<open>zs ! j = the (H (arr + j - 1))\<close> by auto

      have "\<And>k. j < k \<and> k < length zs \<Longrightarrow> zs ! k = xs ! k"
        using \<open>\<And>k. k < length zs \<Longrightarrow> zs ! k = (if k = j - 1 then the (H (arr + j)) else if k = j then the (H (arr + j - 1)) else xs ! k)\<close> by auto
      have "\<And>k. j < k \<and> k < length zs \<Longrightarrow> zs ! j \<le> zs ! k"
      proof-
        fix k 
        assume "j < k \<and> k < length zs"
        have "zs ! j = the (H (arr + j - 1))"
          using \<open>zs ! j = the (H (arr + j - 1))\<close> by blast
        have "zs ! k = xs ! k"
          using \<open>\<And>k. j < k \<and> k < length zs \<Longrightarrow> zs ! k = xs ! k\<close> \<open>j < k \<and> k < length zs\<close> by blast
        also have "xs ! k = (removeAt j xs) ! (k - 1)"
          by (smt One_nat_def Suc_leI Suc_pred \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>j < i - 1\<close> \<open>j < k \<and> k < length zs\<close> \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> array_length leD le_add_diff_inverse2 less_trans removeAt_at)
        finally have "zs ! k = (removeAt j xs) ! (k - 1)"
          by simp

        have "\<And>k. j \<le> k \<and> k < length (removeAt j xs) \<Longrightarrow> (removeAt j xs) ! (j - 1) \<le> (removeAt j xs) ! k"
          by (metis \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> diff_le_self less_imp_diff_less nat_less_le sorted_nth_mono)
        have "removeAt j xs ! (j - 1) = the (H (arr + j - 1))"
          by (metis One_nat_def \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>j < i - 1\<close> \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> \<open>xs ! (j - 1) = the (H (arr + j - 1))\<close> array_length diff_Suc_less removeAt_at)

        show "zs ! j \<le> zs ! k"
          by (metis (no_types, lifting) One_nat_def Suc_leI Suc_pred \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>\<And>k. j \<le> k \<and> k < length (removeAt j xs) \<Longrightarrow> removeAt j xs ! (j - 1) \<le> removeAt j xs ! k\<close> \<open>j < k \<and> k < length zs\<close> \<open>j \<le> i \<and> array H arr (i - 1) xs \<and> sorted (removeAt j xs)\<close> \<open>length zs = i - 1\<close> \<open>removeAt j xs ! (j - 1) = the (H (arr + j - 1))\<close> \<open>zs ! j = the (H (arr + j - 1))\<close> \<open>zs ! k = removeAt j xs ! (k - 1)\<close> array_length diff_less_mono less_trans removeAt_length)
      qed

      have "sorted (removeAt (j - 1) zs)"
      proof-
        { fix k
          assume "k < length (removeAt (j - 1) zs)"

          have "k < j - 1 \<Longrightarrow> (removeAt (j - 1) zs) ! k \<le> (removeAt (j - 1) zs) ! (j - 1)"
            by (metis One_nat_def Suc_leI \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>\<And>k. k < j - 1 \<Longrightarrow> zs ! k \<le> zs ! j\<close> \<open>j < i - 1\<close> \<open>length zs = i - 1\<close> le_add_diff_inverse2 less_imp_diff_less neq_iff removeAt_at)
          have "j \<le> k \<Longrightarrow> (removeAt (j - 1) zs) ! (j - 1) \<le> (removeAt (j - 1) zs) ! k"
            by (smt One_nat_def Suc_less_eq \<open>(\<exists>zs'. j \<le> i \<and> array H arr (i - 1) zs' \<and> sorted (removeAt j zs')) \<and> 0 < j \<and> the (H (arr + j)) < the (H (arr + j - 1))\<close> \<open>\<And>k. j < k \<and> k < length zs \<Longrightarrow> zs ! j \<le> zs ! k\<close> \<open>j < i - 1\<close> \<open>k < length (removeAt (j - 1) zs)\<close> \<open>length zs = i - 1\<close> add.commute leD le_add_diff_inverse2 less_Suc_eq less_Suc_eq_le less_trans plus_1_eq_Suc removeAt_at removeAt_length)

          have "sorted (take (j - 2) (removeAt (j - 1) zs))"
          proof-
            have "take (j - 2) (removeAt (j - 1) zs) = take (j - 2) (removeAt j xs)"

        }
    }

    have "sorted (removeAt (j - 1) zs)"
    proof-
      have "zs ! (j - 1) = xs ! j"

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
