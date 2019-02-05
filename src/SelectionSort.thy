theory SelectionSort
  imports Main IOArray
begin

fun selection_sort :: "nat io_array \<Rightarrow> unit io" where
  "selection_sort arr = (let n = get_size arr in forMu (map nat [1..int n]) (\<lambda>i. do {
    min_ref \<leftarrow> ref i;
    forMu (map nat [int i+1..int n]) (\<lambda>j. do {
      valJ \<leftarrow> read_array arr j;
      m \<leftarrow> ! min_ref;
      valMin \<leftarrow> read_array arr m;
      whenu (valJ < valMin) (min_ref := j)
    });
    m \<leftarrow> ! min_ref;
    swap_array arr i m;
    return ()
  }))"

export_code selection_sort in Haskell
  module_name SelectionSort file "gen/"

primrec sorted :: "'a::ord list \<Rightarrow> bool" where
  "sorted [] = True"
| "sorted (x#xs) = ((\<forall>y\<in>set xs. x \<le> y) \<and> sorted xs)"

fun selection_sort_program where
  "selection_sort_program xs = do {
    arr \<leftarrow> new_array_from_list xs;
    selection_sort arr;
    read_array_as_list arr
  }"

theorem selection_sort_is_sorted:
  assumes "effect (run_io (selection_sort_program xs)) h h' rs"
  shows "sorted rs"
  sorry

end
