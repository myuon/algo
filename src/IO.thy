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

datatype addr = Addr nat
type_synonym heap_rep = nat

record heap = 
  memory :: "addr \<Rightarrow> typerep"
  lim :: nat

datatype 'a ref = Ref addr

primrec nat_of_addr where
  "nat_of_addr (Addr n) = n"

lemma nat_of_addr_inj [simp]:
  "nat_of_addr r = nat_of_addr r' \<longleftrightarrow> r = r'"
  by (cases r, cases r') simp_all

primrec addr_of_ref :: "'a ref \<Rightarrow> addr" where
  "addr_of_ref (Ref r) = r"

lemma addr_of_ref_inj [simp]:
  "addr_of_ref r = addr_of_ref r' \<longleftrightarrow> r = r'"
  by (cases r, cases r') simp_all

primrec nat_of_ref :: "'a ref \<Rightarrow> nat" where
  "nat_of_ref (Ref r) = (case r of Addr a \<Rightarrow> a)"

instance ref :: (type) countable
  apply (rule countable_classI [of nat_of_ref])
  apply (metis addr.case addr.exhaust nat_of_ref.simps ref.exhaust)
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

lemma bind_execute[simp]: "execute (m \<bind> k) h = (case (execute m h) of (val,h') \<Rightarrow> execute (k val) h')"
  by (simp add: IO.bind_def)

code_printing
  type_constructor io \<rightharpoonup> (Haskell) "IO _"
  | type_constructor ref \<rightharpoonup> (Haskell) "IORef _"
  | constant return \<rightharpoonup> (Haskell) "return"
  | constant bind \<rightharpoonup> (Haskell) infixl 5 ">>="

end
