theory IO
  imports Main "HOL-Imperative_HOL.Imperative_HOL"
begin

datatype 'a io = IO (run_io: "'a Heap")

definition return :: "'a \<Rightarrow> 'a io" where
  [code del]: "return x = IO (Heap_Monad.return x)"

definition bind :: "'a io \<Rightarrow> ('a \<Rightarrow> 'b io) \<Rightarrow> 'b io" where
  [code del]: "bind x f = IO (Heap_Monad.bind (run_io x) (run_io \<circ> f))"

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

definition execute_io where
  "execute_io c h = execute (run_io c) h"

definition effect_io where
  "effect_io c h h' r = (execute_io c h = Some (r,h'))"

lemma bind_execute[simp]: "execute (m \<bind> k) h = (execute m h) \<bind> (\<lambda>(val,h'). execute (k val) h')"
proof -
  have "\<forall>z f za. (case za of None \<Rightarrow> z::('a \<times> heap) option | Some (x::'b \<times> heap) \<Rightarrow> f x) = za \<bind> f \<or> za = None"
    by fastforce
  then show ?thesis
    by (metis (no_types) bind.bind_lzero execute_bind(2) execute_bind_case)
qed

lemma io_bind_execute[simp]: "execute_io (m \<bind> k) h = (execute_io m h) \<bind> (\<lambda>(val,h'). execute_io (k val) h')"
  by (simp add: IO.bind_def execute_io_def)

code_printing code_module "IO" \<rightharpoonup> (Haskell)
\<open>import qualified Data.Vector\<close>

code_printing code_module "Heap" \<rightharpoonup> (Haskell)

code_printing
  type_constructor io \<rightharpoonup> (Haskell) "IO _"
  | type_constructor ref \<rightharpoonup> (Haskell) "IORef _"
  | type_constructor array \<rightharpoonup> (Haskell) "V.IOVector _"
  | constant return \<rightharpoonup> (Haskell) "return"
  | constant bind \<rightharpoonup> (Haskell) infixl 5 ">>="

end
