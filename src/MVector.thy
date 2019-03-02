theory MVector
  imports IO
begin

datatype 'a mvector = MVector addr nat

primrec addr_of_mvector where
  "addr_of_mvector (MVector a _) = a"

primrec size_of_mvector where
  "size_of_mvector (MVector _ s) = s"

definition alloc :: "nat \<Rightarrow> heap \<Rightarrow> 'a::heap mvector \<times> heap" where
  "alloc n h = (let l = lim h; r = MVector l n in (r, h \<lparr> lim := lim h + n \<rparr>))"

definition get_at :: "heap \<Rightarrow> 'a::heap mvector \<Rightarrow> nat \<Rightarrow> 'a" where
  "get_at h v i = from_nat (memory h (addr_of_mvector v + i))"

definition set_at :: "'a::heap mvector \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "set_at r j v h = h \<lparr> memory := (\<lambda>i. if i = addr_of_mvector r + j then to_nat v else memory h i) \<rparr>"

definition new :: "nat \<Rightarrow> 'a::heap mvector io" where
  "new n = IO (alloc n)"

definition read :: "'a::heap mvector \<Rightarrow> nat \<Rightarrow> 'a io" where
  "read vec i = tap (\<lambda>h. get_at h vec i)"

definition writ :: "'a::heap mvector \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> unit io" where
  "writ vec i v = IO (\<lambda>h. ((), set_at vec i v h))"

definition modify :: "'a::heap mvector \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> unit io" where
  "modify vec f i = read vec i \<bind> (\<lambda>x. writ vec i (f x))"

definition swap :: "'a::heap mvector \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit io" where
  "swap arr i j = do {
    valI \<leftarrow> read arr i;
    valJ \<leftarrow> read arr j;
    writ arr j valI;
    writ arr i valJ;
    return ()
  }"

lemma get_set_eq [simp]: "get_at (set_at r i x h) r i = x"
  by (simp add: get_at_def set_at_def)

lemma get_set_neq: "i \<noteq> j \<Longrightarrow> get_at (set_at r i x h) r j = get_at h r j"
  apply (auto simp add: get_at_def set_at_def)
  done

lemma set_same [simp]: "set_at r j x (set_at r j y h) = set_at r j x h"
  apply (simp add: set_at_def)
proof-
  have "\<And>P x y. P x \<Longrightarrow> (\<And>y. x \<noteq> y \<Longrightarrow> P y) \<Longrightarrow> (\<And>z. P z)"
    by metis
  hence "\<And>f g. f (addr_of_mvector r + j) = g (addr_of_mvector r + j)
    \<Longrightarrow> (\<And>x. x \<noteq> addr_of_mvector r + j \<Longrightarrow> f x = g x) \<Longrightarrow> (\<And>z. f z = g z)"
    by smt
  hence "\<And>z. (\<lambda>i. if i = addr_of_mvector r + j then to_nat x else memory (h\<lparr>memory := \<lambda>i. if i = addr_of_mvector r + j then to_nat y else memory h i\<rparr>) i) z
    = (\<lambda>i. if i = addr_of_mvector r + j then to_nat x else memory h i) z"
    by auto
  thus "h\<lparr>memory := \<lambda>i. if i = addr_of_mvector r + j then to_nat x else memory (h\<lparr>memory := \<lambda>i. if i = addr_of_mvector r + j then to_nat y else memory h i\<rparr>) i\<rparr>
    = h\<lparr>memory := \<lambda>i. if i = addr_of_mvector r + j then to_nat x else memory h i\<rparr>"
    by simp
qed

lemma execute_new: "execute (new n) h = alloc n h"
  by (simp add: new_def)

lemma execute_read: "execute (read v i) h = (get_at h v i, h)"
  by (simp add: read_def execute_def get_at_def tap_def)

lemma execute_writ: "execute (writ r i v) h = ((), set_at r i v h)"
  by (simp add: writ_def)

lemma effect_read:
  assumes "effect (read arr i) h h' r"
  shows "r = get_at h arr i" "h = h'"
  apply (metis assms effectE execute_read prod.sel(1))
  apply (metis assms effectE execute_tap read_def snd_conv)
  done

lemma effect_writ:
  assumes "effect (writ arr i v) h h' ()"
  shows "h' = set_at arr i v h"
  by (metis (full_types) assms effectE execute_writ snd_conv)

lemma effect_swap:
  assumes "effect (swap arr i j) h h' ()"
  and "i \<noteq> j"
  shows "get_at h' arr i = get_at h arr j" and "get_at h' arr j = get_at h arr i"
proof-
  obtain h1 ri rj where
    "effect (read arr i) h h ri"
    "effect (read arr j) h h rj"
    "effect (writ arr j ri) h h1 ()"
    "effect (writ arr i rj) h1 h' ()"
  proof-
    have "effect (do {
      ri \<leftarrow> read arr i;
      rj \<leftarrow> read arr j;
      writ arr j ri;
      writ arr i rj;
      return ()
    }) h h' ()"
      using assms
      by (simp add: swap_def)
    then obtain ri where
      e1: "effect (read arr i) h h ri"
      "effect (do {
        rj \<leftarrow> read arr j;
        writ arr j ri;
        writ arr i rj;
        return ()
      }) h h' ()"
      by (metis (no_types, lifting) effect_bind effect_read(2))
    then obtain rj where
      e2: "effect (read arr j) h h rj"
      "effect (do {
        writ arr j ri;
        writ arr i rj;
        return ()
      }) h h' ()"
      by (metis (no_types, lifting) effect_bind effect_read(2))
    then obtain h1 where
      e3: "effect (writ arr j ri) h h1 ()"
      "effect (do { writ arr i rj; return () }) h1 h' ()"
      using effect_bind by force
    hence e4: "effect (writ arr i rj) h1 h' ()"
      by simp

    assume H: "(\<And>ri rj h1. effect (read arr i) h h ri \<Longrightarrow> effect (read arr j) h h rj \<Longrightarrow> effect (writ arr j ri) h h1 () \<Longrightarrow> effect (writ arr i rj) h1 h' () \<Longrightarrow> thesis)"
    show ?thesis
      apply (rule H)
      apply (rule e1)
      apply (rule e2)
      apply (rule e3)
      apply (rule e4)
      done
  qed

  have "ri = get_at h arr i"
    using \<open>effect (read arr i) h h ri\<close> effect_read(1) by blast
  have "rj = get_at h arr j"
    using \<open>effect (read arr j) h h rj\<close> effect_read(1) by blast
  have h': "h' = set_at arr i rj (set_at arr j ri h)"
    using \<open>effect (writ arr i rj) h1 h' ()\<close> \<open>effect (writ arr j ri) h h1 ()\<close> effect_writ by blast

  show "get_at h' arr i = get_at h arr j"
    apply (simp add: h')
    by (simp add: \<open>rj = get_at h arr j\<close>)
  show "get_at h' arr j = get_at h arr i"
    apply (simp add: h')
    by (simp add: \<open>ri = get_at h arr i\<close> assms(2) get_set_neq)
qed


(*
fast implementation

definition from_list :: "'a::heap list \<Rightarrow> 'a mvector io" where
  "from_list xs = fold (\<lambda>(i,x) m. m \<bind> (\<lambda>vec. writ vec i x \<bind> (\<lambda>_. return vec))) (enumerate 0 xs) (new (size xs))"
*)

primrec from_list_pr :: "'a::heap mvector \<Rightarrow> 'a::heap list \<Rightarrow> nat \<Rightarrow> 'a mvector io" where
  "from_list_pr mvec [] n = return mvec"
| "from_list_pr mvec (x#xs) n = writ mvec n x \<bind> (\<lambda>_. from_list_pr mvec xs (Suc n))"

definition from_list :: "'a::heap list \<Rightarrow> 'a mvector io" where
  "from_list xs = new (size xs) \<bind> (\<lambda>mvec. from_list_pr mvec xs 0)"

definition to_list :: "'a::heap mvector \<Rightarrow> 'a list io" where
  "to_list vec = (let s = size_of_mvector vec in mapM (read vec) [0..<s])"

definition set_over :: "'a::heap mvector \<Rightarrow> 'a::heap list \<Rightarrow> heap \<Rightarrow> heap" where
  "set_over r xs h = h \<lparr> memory := (\<lambda>i. if lim h < i \<and> i < lim h + size xs then to_nat (get_at h r (i - lim h)) else memory h i) \<rparr>"

lemma execute_from_list: "execute (from_list xs) h = (case alloc (size xs) h of (mvec,h0) \<Rightarrow> (mvec, fold (\<lambda>(i,x) h. set_at mvec i x h) (enumerate 0 xs) h0))"
proof-
  have "\<And>mvec h' i. execute (from_list_pr mvec xs i) h' = (mvec, fold (\<lambda>(i, x). set_at mvec i x) (enumerate i xs) h')"
    apply (induct xs, simp add: return_def)
    apply (simp add: execute_writ execute_bind)
    done
  thus "execute (from_list xs) h = (case alloc (size xs) h of (mvec,h0) \<Rightarrow> (mvec, fold (\<lambda>(i,x) h. set_at mvec i x h) (enumerate 0 xs) h0))"
    apply (simp add: from_list_def execute_new execute_bind)
    done
qed

definition get_over_internal where
  "get_over_internal mvec h n = map (get_at h mvec) [0..<n]"

definition get_over :: "'a::heap mvector \<Rightarrow> heap \<Rightarrow> 'a list" where
  "get_over mvec h = get_over_internal mvec h (size_of_mvector mvec)"

lemma mapM_append: "execute (mapM f (xs @ ys)) h = execute (do {
  rx \<leftarrow> mapM f xs;
  ry \<leftarrow> mapM f ys;
  return (rx @ ry)
}) h"
  apply (induct xs arbitrary: ys h, simp)
proof-
  have f: "\<And>x y z h. execute (x \<bind> (\<lambda>b. (y \<bind> (\<lambda>rx. z \<bind> (\<lambda>ry. return (rx @ ry)))) \<bind> (\<lambda>c. return (b # c)))) h =
                     execute (x \<bind> (\<lambda>b. y \<bind> (\<lambda>rx. z \<bind> (\<lambda>ry. return (rx @ ry) \<bind> (\<lambda>c. return (b # c)))))) h"
    by (smt execute_bind split_def)

  fix a xs ys h
  assume p: "\<And>ys h. execute (mapM f (xs @ ys)) h = execute (do {
    rx \<leftarrow> mapM f xs;
    ry \<leftarrow> mapM f ys;
    return (rx @ ry)
  }) h"
  have "execute (mapM f ((a # xs) @ ys)) h = execute (do {
    b \<leftarrow> f a;
    c \<leftarrow> mapM f (xs @ ys);
    return (b#c)
  }) h"
    by (simp)
  also have "\<dots> = execute (do {
    b \<leftarrow> f a;
    c \<leftarrow> do {
      rx \<leftarrow> mapM f xs;
      ry \<leftarrow> mapM f ys;
      return (rx @ ry)
    };
    return (b#c)
  }) h"
    by (simp add: p return_def execute_bind)
  also have "\<dots> = execute (do {
    b \<leftarrow> f a;
    rx \<leftarrow> mapM f xs;
    ry \<leftarrow> mapM f ys;
    c \<leftarrow> return (rx @ ry);
    return (b#c)
  }) h"
    using f [of "f a" "mapM f xs" "mapM f ys" h] by simp
  also have "\<dots> = execute (do {
    b \<leftarrow> f a;
    rx \<leftarrow> mapM f xs;
    ry \<leftarrow> mapM f ys;
    return ((b # rx) @ ry)
  }) h"
  proof-
    have "\<And>rx ry b h. execute (do { c \<leftarrow> return (rx @ ry); return (b#c) }) h = execute (do { return (b # rx @ ry) }) h"
      by (simp add: return_def execute_bind)
    hence "\<And>x p q h. execute (do { b \<leftarrow> x; rx \<leftarrow> p; ry \<leftarrow> q; c \<leftarrow> return (rx @ ry); return (b#c) }) h
                   = execute (do { b \<leftarrow> x; rx \<leftarrow> p; ry \<leftarrow> q; return (b # (rx @ ry)) }) h"
      by (simp add: return_def execute_bind)
    thus ?thesis
      by (simp add: return_def)
  qed
  also have "\<dots> = execute (do {
    b \<leftarrow> f a;
    rx \<leftarrow> mapM f xs;
    brx \<leftarrow> return (b # rx);
    ry \<leftarrow> mapM f ys;
    return (brx @ ry)
  }) h"
  proof-
    have "\<And>b rx. do { ry \<leftarrow> mapM f ys; return (b # rx @ ry) } = do { brx \<leftarrow> return (b # rx); ry \<leftarrow> mapM f ys; return (brx @ ry) }"
      by (simp)
    thus ?thesis
      by simp
  qed
  also have "\<dots> = execute (do {
    brx \<leftarrow> mapM f (a # xs);
    ry \<leftarrow> mapM f ys;
    return (brx @ ry)
  }) h"
  proof-
    have hyp: "do { b \<leftarrow> f a; rx \<leftarrow> mapM f xs; return (b # rx) } = do { mapM f (a # xs) }"
      by simp
    show ?thesis
      apply (subst hyp [symmetric])
      by (smt execute_bind split_def)
  qed
  finally show "execute (mapM f ((a # xs) @ ys)) h = execute (mapM f (a # xs) \<bind> (\<lambda>rx. mapM f ys \<bind> (\<lambda>ry. return (rx @ ry)))) h"
    by simp
qed

lemma execute_to_list: "execute (to_list mvec) h = (get_over mvec h, h)"
  apply (simp add: to_list_def get_over_def)
proof-
  have "\<And>n. execute (mapM (read mvec) [0..<n]) h = (get_over_internal mvec h n, h)"
  proof-
    fix n
    show "execute (mapM (read mvec) [0..<n]) h = (get_over_internal mvec h n, h)"
      apply (induct n arbitrary: h)
      apply (simp add: get_over_internal_def return_def)
      apply (simp add: get_over_internal_def mapM_append)
    proof-
      fix n h
      assume "\<And>h. execute (mapM (read mvec) [0..<n]) h = (map (get_at h mvec) [0..<n], h)"
      hence "execute (mapM (read mvec) [0..<n] \<bind> (\<lambda>rx. read mvec n \<bind> (\<lambda>x. return (rx @ [x])))) h = (let rx = map (get_at h mvec) [0..<n] in execute (read mvec n \<bind> (\<lambda>x. return (rx @ [x]))) h)"
        by (simp add: execute_bind)
      also have "\<dots> = (map (get_at h mvec) [0..<n] @ [get_at h mvec n], h)"
        by (simp add: execute_bind execute_read return_def)
      finally show "execute (mapM (read mvec) [0..<n] \<bind> (\<lambda>rx. read mvec n \<bind> (\<lambda>x. return (rx @ [x])))) h = (map (get_at h mvec) [0..<n] @ [get_at h mvec n], h)"
        by simp
    qed
  qed

  thus "execute (mapM (read mvec) [0..<size_of_mvector mvec]) h = (get_over_internal mvec h (size_of_mvector mvec), h)"
    by simp
qed

definition ref_not_in :: "'a::heap ref \<Rightarrow> 'b::heap mvector \<Rightarrow> bool" where
  "ref_not_in r arr = (\<forall>i\<in>set [0..<size_of_mvector arr]. r =!= (Ref (addr_of_mvector arr + i) :: 'b::heap ref))"

lemma get_at_as_ref:
  "get_at h arr i = IO.get h (Ref (addr_of_mvector arr + i))"
  apply (simp add: get_at_def IO.get_def)
  done

lemma set_at_as_ref:
  "set_at arr i val h = IO.set (Ref (addr_of_mvector arr + i)) val h"
  apply (simp add: set_at_def IO.set_def)
  done

definition present_in where
  "present_in arr n = (n \<in> set [0..<size_of_mvector arr])"

lemma ref_not_in_irrelative:
  assumes "ref_not_in r arr"
  and "present_in arr i"
  shows "get_at (IO.set r val h) arr i = get_at h arr i"
  and "IO.get (set_at arr i val h) r = IO.get h r"
proof-
  have "r =!= Ref (addr_of_mvector arr + i)"
    by (metis addr_of_ref.simps assms(1) assms(2) noteq_def ref_not_in_def present_in_def)
  show "get_at (IO.set r val h) arr i = get_at h arr i"
    apply (simp add: get_at_as_ref)
    apply (simp add: \<open>r =!= Ref (addr_of_mvector arr + i)\<close> noteq_set_get)
    done
next
  have "r =!= Ref (addr_of_mvector arr + i)"
    by (metis addr_of_ref.simps assms(1) assms(2) noteq_def ref_not_in_def present_in_def)
  show "IO.get (set_at arr i val h) r = IO.get h r"
    apply (simp add: set_at_as_ref)
    apply (simp add: \<open>r =!= Ref (addr_of_mvector arr + i)\<close> noteq_set_get noteq_sym)
    done
qed

end
