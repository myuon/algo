theory Array
  imports IO
begin

fun write_list_as_array :: "'a::repr list \<Rightarrow> 'a array io" where
  "write_list_as_array xs = (do {
    arr \<leftarrow> new_array (size xs);
    forMu (enumerate 0 xs) (\<lambda>(i,x). write_array arr i x);
    return arr
  })"

fun read_list_from_array :: "'a::repr array \<Rightarrow> 'a list io" where
  "read_list_from_array (Array arr n) = mapM (\<lambda>i. read_array (Array arr n) i) (map nat [0..int n])"

lemma list_write_read_id: "write_list_as_array xs \<bind> (\<lambda>arr. read_list_from_array arr) = return xs"
  apply (induction xs)
  apply (simp add: monad_assoc monad_left_id)

end
