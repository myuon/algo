theory SelectionSort
  imports Main IO "HOL-Library.Monad_Syntax"
begin

fun selection_sort :: "nat array \<Rightarrow> nat \<Rightarrow> unit io" where
  "selection_sort arr n = forMu (map nat [1..int n]) (\<lambda>i. do {
    minRef \<leftarrow> new i;
    forMu (map nat [int i+1..int n]) (\<lambda>j. do {
      valJ \<leftarrow> read_array arr j;
      min \<leftarrow> get minRef;
      valMin \<leftarrow> read_array arr min;
      whenu (valJ < valMin) (put minRef j)
    });
    min \<leftarrow> get minRef;
    swap_array arr i min;
    return ()
  })"

export_code selection_sort in Haskell
  module_name SelectionSort file "gen/"


end
