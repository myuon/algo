theory IO
  imports Main "HOL-Imperative_HOL.Array"
begin
                              
datatype 'a io = IO (run_io: "'a Heap")

definition return :: "'a \<Rightarrow> 'a io" where
  "return x = IO (Heap_Monad.return x)"

definition bind :: "'a io \<Rightarrow> ('a \<Rightarrow> 'b io) \<Rightarrow> 'b io" where
  "bind x f = IO (Heap_Monad.bind (run_io x) (run_io \<circ> f))"

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

definition present :: "heap \<Rightarrow> 'a::heap ref \<Rightarrow> bool" where
  "present h r \<longleftrightarrow> addr_of_ref r < lim h"

definition get :: "heap \<Rightarrow> 'a::heap ref \<Rightarrow> 'a" where
  "get h = from_nat \<circ> refs h TYPEREP('a) \<circ> addr_of_ref"

definition set :: "'a::heap ref \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "set r x = refs_update
    (\<lambda>h. h(TYPEREP('a) := ((h (TYPEREP('a))) (addr_of_ref r := to_nat x))))"

definition alloc :: "nat \<Rightarrow> heap \<Rightarrow> 'a::heap ref \<times> heap" where
  "alloc s h = (let
     l = lim h;
     r = Ref l
   in (r, (h\<lparr>lim := l + s\<rparr>)))"

definition new :: "'a \<Rightarrow> heap \<Rightarrow> 'a::heap ref \<times> heap" where
  "new v h = (case alloc 1 h of (aref,h') \<Rightarrow> (aref, set aref v h'))"

definition noteq :: "'a::heap ref \<Rightarrow> 'b::heap ref \<Rightarrow> bool" (infix "=!=" 70) where
  "r =!= s \<longleftrightarrow> TYPEREP('a) \<noteq> TYPEREP('b) \<or> addr_of_ref r \<noteq> addr_of_ref s"

definition allocate :: "nat \<Rightarrow> 'a::heap ref io" where
  "allocate s = IO (Heap_Monad.heap (alloc s))"

definition ref :: "'a::heap \<Rightarrow> 'a ref io" where
  [code del]: "ref v = IO (Heap_Monad.heap (new v))"

definition lookup :: "'a::heap ref \<Rightarrow> 'a io" ("!_" 61) where
  [code del]: "lookup r = IO (Heap_Monad.tap (\<lambda>h. get h r))"

definition update :: "'a ref \<Rightarrow> 'a::heap \<Rightarrow> unit io" ("_ := _" 62) where
  [code del]: "update r v = IO (Heap_Monad.heap (\<lambda>h. ((), set r v h)))"

definition modify :: "('a::heap \<Rightarrow> 'a) \<Rightarrow> 'a ref \<Rightarrow> 'a io" where
  "modify f r = do {
     x \<leftarrow> ! r;
     let y = f x;
     r := y;
     return y
   }"

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

(*
code_printing
  type_constructor io \<rightharpoonup> (Haskell) "IO _"
  | type_constructor ref \<rightharpoonup> (Haskell) "IORef _"
  | type_constructor array \<rightharpoonup> (Haskell) "V.IOVector _"
  | constant return \<rightharpoonup> (Haskell) "return"
  | constant ref \<rightharpoonup> (Haskell) "newIORef"
  | constant look \<rightharpoonup> (Haskell) "readIORef"
  | constant put \<rightharpoonup> (Haskell) "writeIORef"
  | constant new_array \<rightharpoonup> (Haskell) "V.unsafeNew"
  | constant read_array \<rightharpoonup> (Haskell) "unsafeRead"
  | constant write_array \<rightharpoonup> (Haskell) "unsafeWrite"
  | constant swap_array \<rightharpoonup> (Haskell) "unsafeSwap"
  | constant forMu \<rightharpoonup> (Haskell) "forM_"
  | constant mapM \<rightharpoonup> (Haskell) "mapM_"
  | constant whenu \<rightharpoonup> (Haskell) "when"
*)

end
