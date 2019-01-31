theory IO
  imports Main "HOL-Library.Countable" "HOL-Library.State_Monad"
begin

class repr = countable

instance nat :: repr ..
instance unit :: repr ..
instance bool :: repr ..
instance int :: repr ..

type_synonym addr = nat

record world =
  memory :: "addr \<Rightarrow> nat"
  used :: "addr"

definition empty_world :: "world" where
  "empty_world = \<lparr> memory = (\<lambda>_. undefined), used = 0 \<rparr>"

datatype 'a ref = Ref addr
datatype 'a array = Array addr

datatype 'a io = IO (run_io: "(world, 'a) state")

definition return :: "'a \<Rightarrow> 'a io" where
  "return x = IO (State_Monad.return x)"

definition bind :: "'a io \<Rightarrow> ('a \<Rightarrow> 'b io) \<Rightarrow> 'b io" where
  "bind x f = IO (run_io x \<bind> (run_io \<circ> f))"

adhoc_overloading
  Monad_Syntax.bind IO.bind

fun new_world :: "'a::repr \<Rightarrow> world \<Rightarrow> 'a ref \<times> world" where
  "new_world val w = (
    let newAddr = used w in
    ( Ref newAddr, \<lparr> memory = \<lambda>i. if i = newAddr then to_nat val else memory w i, used = newAddr + 1 \<rparr> )
  )"

fun alloc_world :: "nat \<Rightarrow> world \<Rightarrow> 'a array \<times> world" where
  "alloc_world s w = (
    ( Array (used w), \<lparr> memory = memory w, used = used w + s \<rparr> )
  )"

fun get_world :: "addr \<Rightarrow> world \<Rightarrow> 'a::repr \<times> world" where
  "get_world addr w = (
    ( from_nat (memory w addr), w )
  )"

fun put_world :: "addr \<Rightarrow> 'a::repr \<Rightarrow> world \<Rightarrow> unit \<times> world" where
  "put_world addr val w = (
    ( (), \<lparr> memory = \<lambda>i. if i = addr then to_nat val else memory w i, used = used w \<rparr> )
  )"

fun new :: "'a::repr \<Rightarrow> 'a ref io" where
  "new val = IO (State (new_world val))"

fun get :: "'a ref \<Rightarrow> 'a::repr io" where
  "get (Ref ref) = IO (State (get_world ref))"

fun put :: "'a ref \<Rightarrow> 'a::repr \<Rightarrow> unit io" where
  "put (Ref ref) val = IO (State (put_world ref val))"

fun new_array :: "nat \<Rightarrow> ('a array) io" where
  "new_array s = IO (State (alloc_world s))"

fun read_array :: "'a array \<Rightarrow> nat \<Rightarrow> 'a::repr io" where
  "read_array (Array arr) i = IO (State (get_world (arr + i)))"

fun write_array :: "'a array \<Rightarrow> nat \<Rightarrow> 'a::repr \<Rightarrow> unit io" where
  "write_array (Array arr) i val = IO (State (put_world (arr + i) val))"

fun swap_array :: "'a::repr array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit io" where
  "swap_array arr i j = do {
    valI \<leftarrow> read_array arr i;
    valJ \<leftarrow> read_array arr j;
    write_array arr j valI;
    write_array arr i valJ;
    return ()
  }"

(* Monadic Combinators *)

fun forMu :: "'a list \<Rightarrow> ('a \<Rightarrow> unit io) \<Rightarrow> unit io" where
  "forMu [] f = return ()"
| "forMu (x#xs) f = f x \<bind> (\<lambda>_. forMu xs f)"

fun whenu :: "bool \<Rightarrow> unit io \<Rightarrow> unit io" where
  "whenu cond f = (if cond then f else return ())"

fun whenM :: "bool io \<Rightarrow> unit io \<Rightarrow> unit io" where
  "whenM cond f = cond \<bind> (\<lambda>b. if b then f else return ())"

declare [[code abort: new_world alloc_world get_world put_world]]

code_printing
  type_constructor io \<rightharpoonup> (Haskell) "IO _"
  | type_constructor ref \<rightharpoonup> (Haskell) "IORef _"
  | type_constructor array \<rightharpoonup> (Haskell) "V.IOVector _"
  | constant return \<rightharpoonup> (Haskell) "return"
  | constant new \<rightharpoonup> (Haskell) "newIORef"
  | constant get \<rightharpoonup> (Haskell) "readIORef"
  | constant put \<rightharpoonup> (Haskell) "writeIORef"
  | constant new_array \<rightharpoonup> (Haskell) "V.unsafeNew"
  | constant read_array \<rightharpoonup> (Haskell) "unsafeRead"
  | constant write_array \<rightharpoonup> (Haskell) "unsafeWrite"
  | constant swap_array \<rightharpoonup> (Haskell) "unsafeSwap"
  | constant forMu \<rightharpoonup> (Haskell) "forM_"
  | constant whenu \<rightharpoonup> (Haskell) "when"

end
