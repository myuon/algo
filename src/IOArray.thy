theory IOArray
  imports IO
begin

datatype 'a io_array = IOArray "'a ref" nat

term "allocate"

fun new_array :: "nat \<Rightarrow> 'a::heap io_array io" where
  "new_array s = allocate s \<bind> (\<lambda>r. return (IOArray r s))"

fun read_array :: "'a io_array \<Rightarrow> nat \<Rightarrow> 'a::heap io" where
  "read_array (IOArray arr _) i = lookup (Ref (addr_of_ref arr + i))"

fun write_array :: "'a io_array \<Rightarrow> nat \<Rightarrow> 'a::heap \<Rightarrow> unit io" where
  "write_array (IOArray arr _) i val = update (Ref (addr_of_ref arr + i)) val"

fun swap_array :: "'a::heap io_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit io" where
  "swap_array arr i j = do {
    valI \<leftarrow> read_array arr i;
    valJ \<leftarrow> read_array arr j;
    write_array arr j valI;
    write_array arr i valJ;
    return ()
  }"

(* IO Operations *)
fun write_list_as_array :: "'a::heap list \<Rightarrow> 'a io_array io" where
  "write_list_as_array xs = (do {
    arr \<leftarrow> new_array (size xs);
    forMu (enumerate 0 xs) (\<lambda>(i,x). write_array arr i x);
    return arr
  })"

fun read_list_from_array :: "'a::heap io_array \<Rightarrow> 'a list io" where
  "read_list_from_array (IOArray arr n) = mapM (\<lambda>i. read_array (IOArray arr n) i) (map nat [0..int n])"

lemma list_write_read_id: "write_list_as_array xs \<bind> (\<lambda>arr. read_list_from_array arr) = return xs"
  sorry

end
