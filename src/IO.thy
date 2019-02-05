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

definition present_heap :: "heap \<Rightarrow> 'a::heap ref \<Rightarrow> bool" where
  "present_heap h r \<longleftrightarrow> addr_of_ref r < lim h"

definition get_heap :: "heap \<Rightarrow> 'a::heap ref \<Rightarrow> 'a" where
  "get_heap h = from_nat \<circ> refs h TYPEREP('a) \<circ> addr_of_ref"

definition set_heap :: "'a::heap ref \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "set_heap r x = refs_update
    (\<lambda>h. h(TYPEREP('a) := ((h (TYPEREP('a))) (addr_of_ref r := to_nat x))))"

definition alloc_heap_array :: "nat \<Rightarrow> heap \<Rightarrow> 'a::heap array \<times> heap" where
  "alloc_heap_array s h = (let
     l = lim h;
     r = Array l
   in (r, (h\<lparr>lim := l + s\<rparr>)))"

definition alloc_heap :: "'a \<Rightarrow> heap \<Rightarrow> 'a::heap ref \<times> heap" where
  "alloc_heap v h = (let
     l = lim h;
     r = Ref l
   in (r, set_heap r v (h\<lparr>lim := l + 1\<rparr>)))"

definition noteq :: "'a::heap ref \<Rightarrow> 'b::heap ref \<Rightarrow> bool" (infix "=!=" 70) where
  "r =!= s \<longleftrightarrow> TYPEREP('a) \<noteq> TYPEREP('b) \<or> addr_of_ref r \<noteq> addr_of_ref s"

definition alloc :: "nat \<Rightarrow> 'a::heap array io" where
  "alloc s = IO (Heap_Monad.heap (alloc_heap_array s))"

definition ref :: "'a::heap \<Rightarrow> 'a ref io" where
  [code del]: "ref v = IO (Heap_Monad.heap (alloc_heap v))"

definition lookup :: "'a::heap ref \<Rightarrow> 'a io" ("!_" 61) where
  [code del]: "lookup r = IO (Heap_Monad.tap (\<lambda>h. get_heap h r))"

definition update :: "'a ref \<Rightarrow> 'a::heap \<Rightarrow> unit io" ("_ := _" 62) where
  [code del]: "update r v = IO (Heap_Monad.heap (\<lambda>h. ((), set_heap r v h)))"

definition modify :: "('a::heap \<Rightarrow> 'a) \<Rightarrow> 'a ref \<Rightarrow> 'a io" where
  "modify f r = do {
     x \<leftarrow> ! r;
     let y = f x;
     r := y;
     return y
   }"

primrec extract_io :: "'a io \<Rightarrow> heap \<Rightarrow> 'a option" where
  "extract_io (IO v) h = map_option fst (execute v h)"

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

lemma set_set_heap [simp]: "set_heap r v2 (set_heap r v1 h) = set_heap r v2 h"
  by (simp add: set_heap_def)

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

lemma execute_alloc: "execute_io (alloc n) h = (let l = lim h in Some (Array l, h \<lparr> lim := l + n \<rparr>))"
  apply (simp add: execute_io_def alloc_def heap_def alloc_heap_array_def)
  apply metis
  done

lemma execute_update: "execute_io (r := v) h = Some ((), (set_heap r v h))"
  by (simp add: update_def effect_io_def execute_io_def heap_def)

lemma effect_update: "effect_io (r := v) h (set_heap r v h) ()"
  by (simp add: update_def effect_io_def execute_io_def heap_def)

lemma update_update: "execute_io (update r v1 \<bind> (\<lambda>_. update r v2)) h = execute_io (update r v2) h"
  by (simp add: execute_update)


end
