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
  "to_list vec = (let s = size_of_mvector vec in mapM (read vec) [0..<s])"

definition set_over :: "'a::heap mvector \<Rightarrow> 'a::heap list \<Rightarrow> heap \<Rightarrow> heap" where
  "set_over r xs h = h \<lparr> memory := (\<lambda>i. if lim h < i \<and> i < lim h + Addr (size xs) then to_nat (get_at h r (nat_of_addr (i - lim h))) else memory h i) \<rparr>"

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

definition get_over :: "'a::heap mvector \<Rightarrow> heap \<Rightarrow> ('a list \<times> heap)" where
  "get_over mvec h = (get_over_internal mvec h (size_of_mvector mvec), h)"

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

lemma execute_to_list: "execute (to_list mvec) h = get_over mvec h"
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

end
