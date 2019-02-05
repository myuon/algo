theory IOArray
  imports IO
begin

datatype 'a io_array = IOArray "'a array" nat

primrec get_array_addr :: "'a::heap io_array \<Rightarrow> addr" where
  "get_array_addr (IOArray a _) = addr_of_array a"

primrec get_size :: "'a io_array \<Rightarrow> nat" where
  "get_size (IOArray _ s) = s"

term "allocate"

definition new_array :: "nat \<Rightarrow> 'a::heap io_array io" where
  "new_array s = alloc s \<bind> (\<lambda>r. return (IOArray r s))"

definition read_array :: "'a io_array \<Rightarrow> nat \<Rightarrow> 'a::heap io" where
  "read_array arr i = lookup (Ref (get_array_addr arr + i))"

definition write_array :: "'a io_array \<Rightarrow> nat \<Rightarrow> 'a::heap \<Rightarrow> unit io" where
  "write_array arr i val = update (Ref (get_array_addr arr + i)) val"

definition swap_array :: "'a::heap io_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit io" where
  "swap_array arr i j = do {
    valI \<leftarrow> read_array arr i;
    valJ \<leftarrow> read_array arr j;
    write_array arr j valI;
    write_array arr i valJ;
    return ()
  }"

lemma execute_write_array: "execute_io (write_array arr n v) h = Some ((), set_heap (Ref (get_array_addr arr + n)) v h)"
  by (simp add: execute_io_def update_def heap_def write_array_def)

lemma write_write_array: "execute_io (write_array arr n x \<bind> (\<lambda>_. write_array arr n y)) h = execute_io (write_array arr n y) h"
  by (simp add: execute_write_array)

(* IO Operations *)
fun new_array_from_list :: "'a::heap list \<Rightarrow> 'a io_array io" where
  "new_array_from_list xs = (do {
    arr \<leftarrow> new_array (size xs);
    forMu (enumerate 0 xs) (\<lambda>(i,x). write_array arr i x);
    return arr
  })"

fun read_array_as_list :: "'a::heap io_array \<Rightarrow> 'a list io" where
  "read_array_as_list (IOArray arr n) = mapM (\<lambda>i. read_array (IOArray arr n) i) (map nat [0..int n])"

lemma effectE_new_array_from_list_index:
  assumes "effect_io (new_array_from_list xs) h h' arr"
  shows "get_array_addr arr = addr_of_array (fst (alloc_heap_array (size xs) h))" "h' = fold (\<lambda>(i,x). set_heap (Ref (get_array_addr arr + i)) x) (enumerate 0 xs) (snd (alloc_heap_array (size xs) h))"
  using assms
  sorry

end
