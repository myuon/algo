theory SelectionSort
  imports Main IO IOArray
begin

fun selection_sort :: "nat io_array \<Rightarrow> nat \<Rightarrow> unit io" where
  "selection_sort arr n = forMu (map nat [1..int n]) (\<lambda>i. do {
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
  })"

export_code selection_sort in Haskell
  module_name SelectionSort file "gen/"

end
