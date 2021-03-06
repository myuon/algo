theory IO
  imports
    Main
    "HOL-Library.Countable"
    "HOL-Library.Monad_Syntax"
begin

(*
  We don't use HOL-Imperative_HOL Library, because it does implement
  arrays as a list in a cell. We will follow the same idea about Heap,
  but implement arrays as sequent cells in a memory.
*)

class heap = typerep + countable

instance unit :: heap ..
instance bool :: heap ..
instance nat :: heap ..
instance int :: heap ..

type_synonym addr = nat

record heap = 
  memory :: "addr \<Rightarrow> nat"
  lim :: addr

datatype 'a ref = Ref addr

primrec addr_of_ref :: "'a ref \<Rightarrow> addr" where
  "addr_of_ref (Ref r) = r"

lemma addr_of_ref_inj [simp]:
  "addr_of_ref r = addr_of_ref r' \<longleftrightarrow> r = r'"
  by (cases r, cases r') simp_all

primrec nat_of_ref :: "'a ref \<Rightarrow> nat" where
  "nat_of_ref (Ref r) = r"

instance ref :: (type) countable
  apply (rule countable_classI [of nat_of_ref])
  apply (metis nat_of_ref.simps ref.exhaust)
  done

instance ref :: (type) heap ..

datatype 'a io = IO "heap \<Rightarrow> ('a \<times> heap)"

primrec execute :: "'a io \<Rightarrow> heap \<Rightarrow> ('a \<times> heap)" where
  [code del]: "execute (IO f) = f"

lemma io_execute [simp]:
  "IO (execute f) = f"
  by (cases f, simp)

definition tap :: "(heap \<Rightarrow> 'a) \<Rightarrow> 'a io" where
  [code del]: "tap f = IO (\<lambda>h. (f h, h))"

lemma execute_tap:
  "execute (tap f) h = (f h, h)"
  by (simp add: tap_def)

definition effect :: "'a io \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> 'a \<Rightarrow> bool" where
  "effect c h h' r = (execute c h = (r,h'))"

lemma effectI: "execute c h = (r,h') \<Longrightarrow> effect c h h' r"
  by (simp add: effect_def)

lemma effectE:
  assumes "effect c h h' r"
  shows "execute c h = (r,h')"
  using assms by (simp add: effect_def)

definition return :: "'a \<Rightarrow> 'a io" where
  [code del]: "return x = IO (\<lambda>h. (x,h))"

definition bind :: "'a io \<Rightarrow> ('a \<Rightarrow> 'b io) \<Rightarrow> 'b io" where
  [code del]: "bind x f = IO (\<lambda>h. case execute x h of (y,h') \<Rightarrow> execute (f y) h')"

adhoc_overloading
  Monad_Syntax.bind IO.bind

(* IO monad *)

lemma monad_left_id[simp]: "return a \<bind> f = f a"
  apply (simp add: return_def bind_def)
  done

lemma monad_right_id[simp]: "m \<bind> return = m"
  apply (simp add: return_def bind_def comp_def)
  done

lemma monad_assoc[simp]:
  fixes m :: "'a::heap io"
  shows "(m \<bind> f) \<bind> g = m \<bind> (\<lambda>x. f x \<bind> g)"
  unfolding bind_def comp_def by (auto split: prod.splits)

(* Monadic Combinators *)

fun forMu :: "'a list \<Rightarrow> ('a \<Rightarrow> unit io) \<Rightarrow> unit io" where
  "forMu [] f = return ()"
| "forMu (x#xs) f = f x \<bind> (\<lambda>_. forMu xs f)"

fun mapM :: "('a \<Rightarrow> 'b::heap io) \<Rightarrow> 'a list \<Rightarrow> 'b list io" where
  "mapM f [] = return []"
| "mapM f (x#xs) = f x \<bind> (\<lambda>r. mapM f xs \<bind> (\<lambda>rs. return (r#rs)))"

fun whenu :: "bool \<Rightarrow> unit io \<Rightarrow> unit io" where
  "whenu cond f = (if cond then f else return ())"

fun whenM :: "bool io \<Rightarrow> unit io \<Rightarrow> unit io" where
  "whenM cond f = cond \<bind> (\<lambda>b. if b then f else return ())"

lemma execute_bind: "execute (m \<bind> k) h = (case (execute m h) of (val,h') \<Rightarrow> execute (k val) h')"
  by (simp add: IO.bind_def)

lemma effect_bind:
  assumes "effect (m \<bind> k) h h' r"
  obtains h'' a where "effect m h h'' a" "effect (k a) h'' h' r"
  using assms
  apply (simp add: effect_def execute_bind)
  by (metis case_prod_beta prod.exhaust_sel)

lemma effect_return_unit [simp]:
  assumes "effect (return ()) h h' ()"
  shows "h' = h"
  by (metis assms effectE execute.simps return_def snd_conv)

lemma forMu_nil [simp]: "execute (forMu [] p) h = ((),h)"
  by (simp add: return_def)

lemma forMu_app_return:
  "execute (forMu (as@bs) program) h = execute (do {
    _ \<leftarrow> forMu as program;
    _ \<leftarrow> forMu bs program;
    return ()
  }) h"
  apply (induct as arbitrary: h, simp)
  apply (simp add: execute_bind)
  done

lemma forMu_app:
  "execute (forMu (as@bs) program) h = execute (do {
    _ \<leftarrow> forMu as program;
    forMu bs program
  }) h"
  apply (induct as arbitrary: h, simp)
  apply (simp add: execute_bind)
  done

code_printing
  type_constructor io \<rightharpoonup> (Haskell) "IO _"
  | type_constructor ref \<rightharpoonup> (Haskell) "IORef _"
  | constant return \<rightharpoonup> (Haskell) "return"
  | constant bind \<rightharpoonup> (Haskell) infixl 5 ">>="

(* Refs *)

definition present :: "heap \<Rightarrow> 'a::heap ref \<Rightarrow> bool" where
  "present h v = (addr_of_ref v < lim h)"

definition set :: "'a::heap ref \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "set r v h = h \<lparr> memory := (\<lambda>i. if i = addr_of_ref r then to_nat v else memory h i) \<rparr>"

definition alloc :: "'a \<Rightarrow> heap \<Rightarrow> 'a::heap ref \<times> heap" where
  "alloc v h = (let l = lim h; r = Ref l in (r, set r v (h \<lparr> lim := lim h + 1 \<rparr>)))"

definition get :: "heap \<Rightarrow> 'a::heap ref \<Rightarrow> 'a" where
  "get h = from_nat \<circ> memory h \<circ> addr_of_ref"

definition ref :: "'a::heap \<Rightarrow> 'a ref io" where
  "ref v = IO (alloc v)"

definition lookup :: "'a::heap ref \<Rightarrow> 'a io" ("!_" 61) where
  "lookup r = tap (\<lambda>h. get h r)"

definition update :: "'a ref \<Rightarrow> 'a::heap \<Rightarrow> unit io" ("_ := _" 62) where
  "update r v = IO (\<lambda>h. ((), set r v h))"

lemma get_set_eq [simp]: "get (set r x h) r = x"
  by (simp add: get_def set_def)

lemma heap_eqI:
  assumes "\<And>x. m1 x = m2 x" and "l1 = l2"
  shows "\<lparr> memory = m1, lim = l1 \<rparr> = \<lparr> memory = m2, lim = l2 \<rparr>"
  using assms by auto

lemma set_same [simp]: "set r x (set r y h) = set r x h"
  apply (simp add: set_def)
proof-
  have "\<And>P x y. P x \<Longrightarrow> (\<And>y. x \<noteq> y \<Longrightarrow> P y) \<Longrightarrow> (\<And>z. P z)"
    by metis
  hence "\<And>f g. f (addr_of_ref r) = g (addr_of_ref r) \<Longrightarrow> (\<And>x. x \<noteq> addr_of_ref r \<Longrightarrow> f x = g x) \<Longrightarrow> (\<And>z. f z = g z)"
    by smt
  hence "\<And>z. (\<lambda>i. if i = addr_of_ref r then to_nat x else memory (h\<lparr>memory := \<lambda>i. if i = addr_of_ref r then to_nat y else memory h i\<rparr>) i) z = (\<lambda>i. if i = addr_of_ref r then to_nat x else memory h i) z"
    by auto
  thus "h\<lparr>memory := \<lambda>i. if i = addr_of_ref r then to_nat x else memory (h\<lparr>memory := \<lambda>i. if i = addr_of_ref r then to_nat y else memory h i\<rparr>) i\<rparr> = h\<lparr>memory := \<lambda>i. if i = addr_of_ref r then to_nat x else memory h i\<rparr>"
    by simp
qed

lemma execute_ref: "execute (ref v) h = alloc v h"
  by (simp add: ref_def)

lemma execute_lookup: "execute (lookup r) h = (get h r, h)"
  by (simp add: lookup_def execute_def tap_def)

lemma execute_update: "execute (update r v) h = ((), set r v h)"
  by (simp add: update_def)

definition noteq :: "'a::heap ref \<Rightarrow> 'b::heap ref \<Rightarrow> bool" (infix "=!=" 70) where
  "r =!= s \<longleftrightarrow> addr_of_ref r \<noteq> addr_of_ref s"

lemma noteq_sym: "r =!= s \<Longrightarrow> s =!= r"
  apply (simp add: noteq_def)
  done

lemma noteq_set_get:
  assumes "r =!= s"
  shows "get (set r val h) s = get h s"
  apply (auto simp add: noteq_def IO.set_def get_def)
  using assms apply (simp add: noteq_def)
  done

lemma effect_forMu_app:
  assumes "effect (forMu (as@bs) program) h h' ()"
  shows "effect (do {
    _ \<leftarrow> forMu as program;
    forMu bs program
  }) h h' ()"
  using assms
  apply (simp add: effect_def)
  apply (simp add: forMu_app)
  done

lemma alloc_get: "alloc v h = (r,h') \<Longrightarrow> get h' r = v"
  apply (simp add: alloc_def get_def)
  by (metis comp_apply get_def get_set_eq prod.sel(1) snd_conv)

hide_const (open) present get set alloc

end
