theory InsertionSort
  imports Main "HOL-Hoare.Separation"
begin

inductive array where
  "array H p 0 []"
| "H p = Some a \<Longrightarrow> array H (p+1) k as \<Longrightarrow> array H p (Suc k) (a#as)"

primrec count where
  "count a [] = 0"
| "count a (x#xs) = (if a = x then Suc (count a xs) else count a xs)"

definition permute where
  "permute xs ys \<equiv> (\<forall>a. count a xs = count a ys)"

lemma "
  VARS H i j
  {array H arr N xs}
  i := 1;
  WHILE i < N INV {emp} DO
    j := i;
    WHILE j > 0 & the (H (arr + j - 1)) > the (H (arr + j)) INV {emp} DO
      tmp := the (H (arr + j));
      H := H (arr + j \<mapsto> the (H (arr + j - 1)));
      H := H (arr + j - 1 \<mapsto> tmp);
      j := j - 1
    OD;
    i := i + 1
  OD
  {array H arr N ys \<and> sorted ys \<and> permute xs ys}
"
  sorry

end
