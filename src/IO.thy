theory IO
  imports Main "HOL-Library.State_Monad"
begin

class repr =
  fixes deserialize :: "typerep \<Rightarrow> 'a"
  and serialize :: "'a \<Rightarrow> typerep"

  assumes ser_de: "serialize \<circ> deserialize = id"
  and de_ser: "deserialize \<circ> serialize = id"

type_synonym addr = nat

record world =
  memory :: "addr \<Rightarrow> typerep"
  used :: "addr"

definition empty_world :: "world" where
  "empty_world = \<lparr> memory = (\<lambda>_. undefined), used = 0 \<rparr>"

datatype 'a ref = Ref addr
datatype 'a array = Array addr

datatype 'a io = IO "(world, 'a) state"

fun new_world :: "'a::repr \<Rightarrow> world \<Rightarrow> 'a ref \<times> world" where
  "new_world val w = (
    let newAddr = used w in
    ( Ref newAddr, \<lparr> memory = \<lambda>i. if i = newAddr then serialize val else memory w i, used = newAddr + 1 \<rparr> )
  )"

fun alloc_world :: "nat \<Rightarrow> world \<Rightarrow> 'a array \<times> world" where
  "alloc_world s w = (
    ( Array (used w), \<lparr> memory = memory w, used = used w + s \<rparr> )
  )"

fun get_world :: "addr \<Rightarrow> world \<Rightarrow> 'a::repr \<times> world" where
  "get_world addr w = (
    ( deserialize (memory w addr), w )
  )"

fun put_world :: "addr \<Rightarrow> 'a::repr \<Rightarrow> world \<Rightarrow> unit \<times> world" where
  "put_world addr val w = (
    ( (), \<lparr> memory = \<lambda>i. if i = addr then serialize val else memory w i, used = used w \<rparr> )
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

end

