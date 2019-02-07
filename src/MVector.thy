theory MVector
  imports IO
begin

datatype 'a mvector = MVector addr nat

primrec addr_of_mvector where
  "addr_of_mvector (MVector a _) = a"

primrec size_of_mvector where
  "size_of_mvector (MVector _ s) = s"

definition alloc :: "nat \<Rightarrow> heap \<Rightarrow> 'a::heap mvector \<times> heap" where
  "alloc n h = (let l = lim h; r = MVector l n in (r, h \<lparr> lim := lim h + Addr n \<rparr>))"

definition get_at :: "heap \<Rightarrow> 'a::heap mvector \<Rightarrow> nat \<Rightarrow> 'a" where
  "get_at h v i = from_nat (memory h (addr_of_mvector v + Addr i))"

definition set_at :: "'a::heap mvector \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "set_at r j v h = h \<lparr> memory := (\<lambda>i. if i = addr_of_mvector r + Addr j then to_nat v else memory h i) \<rparr>"

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

lemma set_same [simp]: "set_at r j x (set_at r j y h) = set_at r j x h"
  apply (simp add: set_at_def)
proof-
  have "\<And>P x y. P x \<Longrightarrow> (\<And>y. x \<noteq> y \<Longrightarrow> P y) \<Longrightarrow> (\<And>z. P z)"
    by metis
  hence "\<And>f g. f (addr_of_mvector r + Addr j) = g (addr_of_mvector r + Addr j)
    \<Longrightarrow> (\<And>x. x \<noteq> addr_of_mvector r + Addr j \<Longrightarrow> f x = g x) \<Longrightarrow> (\<And>z. f z = g z)"
    by smt
  hence "\<And>z. (\<lambda>i. if i = addr_of_mvector r + Addr j then to_nat x else memory (h\<lparr>memory := \<lambda>i. if i = addr_of_mvector r + Addr j then to_nat y else memory h i\<rparr>) i) z
    = (\<lambda>i. if i = addr_of_mvector r + Addr j then to_nat x else memory h i) z"
    by auto
  thus "h\<lparr>memory := \<lambda>i. if i = addr_of_mvector r + Addr j then to_nat x else memory (h\<lparr>memory := \<lambda>i. if i = addr_of_mvector r + Addr j then to_nat y else memory h i\<rparr>) i\<rparr>
    = h\<lparr>memory := \<lambda>i. if i = addr_of_mvector r + Addr j then to_nat x else memory h i\<rparr>"
    by simp
qed

lemma execute_new: "execute (new n) h = alloc n h"
  by (simp add: new_def)

lemma execute_read: "execute (read v i) h = (get_at h v i, h)"
  by (simp add: read_def execute_def get_at_def tap_def)

lemma execute_writ: "execute (writ r i v) h = ((), set_at r i v h)"
  by (simp add: writ_def)

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
  "to_list vec = (let s = size_of_mvector vec in mapM (\<lambda>i. read vec (nat i)) [0..int s])"

definition set_over :: "'a::heap mvector \<Rightarrow> 'a::heap list \<Rightarrow> heap \<Rightarrow> heap" where
  "set_over r xs h = h \<lparr> memory := (\<lambda>i. if lim h < i \<and> i < lim h + Addr (size xs) then to_nat (get_at h r (nat_of_addr (i - lim h))) else memory h i) \<rparr>"

primrec snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = [x]"
| "snoc (y#ys) x = y # snoc ys x"

lemma snoc_length: "length (snoc ys y) = Suc (length ys)"
  by (induct ys, auto)

lemma snoc_induct:
  assumes "P []"
  and "\<And>xs y. P xs \<Longrightarrow> P (snoc xs y)"
  shows "P xs"
  apply (induct "size xs" arbitrary: xs)
  apply (simp add: assms(1))
proof-
  have cons_snoc: "\<And>(a :: 'a list) x xs. a = x # xs \<Longrightarrow> \<exists>y ys. a = snoc ys y"
  proof-
    fix a :: "'a list" and x xs
    show cons_snoc: "a = x # xs \<Longrightarrow> \<exists>y ys. a = snoc ys y"
      apply (induct a arbitrary: x xs, auto)
    proof-
      fix x :: 'a and xs
      assume "\<And>x (xsa :: 'a list). xs = x # xsa \<Longrightarrow> \<exists>y ys. x # xsa = snoc ys y"
      show "\<exists>y ys. x # xs = snoc ys y"
        apply (cases xs)
        apply (metis snoc.simps(1))
        by (metis \<open>\<And>xsa xa. xs = xa # xsa \<Longrightarrow> \<exists>y ys. xa # xsa = snoc ys y\<close> snoc.simps(2))
    qed
  qed

  fix x and xs :: "'a list"
  assume "\<And>xs. x = length xs \<Longrightarrow> P xs"
  and "Suc x = length xs"
  obtain y ys where "xs = y # ys"
    by (meson Suc_length_conv \<open>Suc x = length xs\<close>)
  then obtain z zs where "xs = snoc zs z"
    using cons_snoc by blast
  hence "x = length zs"
    by (simp add: Suc_inject \<open>Suc x = length xs\<close> snoc_length)
  show "P xs"
    by (simp add: \<open>\<And>xs. x = length xs \<Longrightarrow> P xs\<close> \<open>x = length zs\<close> \<open>xs = snoc zs z\<close> assms(2))
qed

lemma execute_from_list: "execute (from_list xs) h = (case alloc (size xs) h of (mvec,h0) \<Rightarrow> (mvec, fold (\<lambda>(i,x) h. set_at mvec i x h) (enumerate 0 xs) h0))"
proof-
  have "\<And>mvec h' i. execute (from_list_pr mvec xs i) h' = (mvec, fold (\<lambda>(i, x). set_at mvec i x) (enumerate i xs) h')"
    apply (induct xs, simp add: return_def)
    apply (simp add: execute_writ)
    done
  thus "execute (from_list xs) h = (case alloc (size xs) h of (mvec,h0) \<Rightarrow> (mvec, fold (\<lambda>(i,x) h. set_at mvec i x h) (enumerate 0 xs) h0))"
    apply (simp add: from_list_def execute_new)
    done
qed

end
