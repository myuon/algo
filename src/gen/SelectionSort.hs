{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SelectionSort(Int, Nat, Io, Ref, Io_array, selection_sort) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Heap;

data Num = One | Bit0 Num | Bit1 Num;

data Int = Zero_int | Pos Num | Neg Num;

one_int :: Int;
one_int = Pos One;

class One a where {
  one :: a;
};

instance One Int where {
  one = one_int;
};

plus_num :: Num -> Num -> Num;
plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One);
plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n);
plus_num (Bit1 m) One = Bit0 (plus_num m One);
plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n);
plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n);
plus_num (Bit0 m) One = Bit1 m;
plus_num One (Bit1 n) = Bit0 (plus_num n One);
plus_num One (Bit0 n) = Bit1 n;
plus_num One One = Bit0 One;

uminus_int :: Int -> Int;
uminus_int (Neg m) = Pos m;
uminus_int (Pos m) = Neg m;
uminus_int Zero_int = Zero_int;

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

dup :: Int -> Int;
dup (Neg n) = Neg (Bit0 n);
dup (Pos n) = Pos (Bit0 n);
dup Zero_int = Zero_int;

plus_int :: Int -> Int -> Int;
plus_int (Neg m) (Neg n) = Neg (plus_num m n);
plus_int (Neg m) (Pos n) = sub n m;
plus_int (Pos m) (Neg n) = sub m n;
plus_int (Pos m) (Pos n) = Pos (plus_num m n);
plus_int Zero_int l = l;
plus_int k Zero_int = k;

sub :: Num -> Num -> Int;
sub (Bit0 m) (Bit1 n) = minus_int (dup (sub m n)) one_int;
sub (Bit1 m) (Bit0 n) = plus_int (dup (sub m n)) one_int;
sub (Bit1 m) (Bit1 n) = dup (sub m n);
sub (Bit0 m) (Bit0 n) = dup (sub m n);
sub One (Bit1 n) = Neg (Bit0 n);
sub One (Bit0 n) = Neg (bitM n);
sub (Bit1 m) One = Pos (Bit0 m);
sub (Bit0 m) One = Pos (bitM m);
sub One One = Zero_int;

minus_int :: Int -> Int -> Int;
minus_int (Neg m) (Neg n) = sub n m;
minus_int (Neg m) (Pos n) = Neg (plus_num m n);
minus_int (Pos m) (Neg n) = Pos (plus_num m n);
minus_int (Pos m) (Pos n) = sub m n;
minus_int Zero_int l = uminus_int l;
minus_int k Zero_int = k;

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Int where {
  plus = plus_int;
};

class Zero a where {
  zero :: a;
};

instance Zero Int where {
  zero = Zero_int;
};

class (Plus a) => Semigroup_add a where {
};

class (One a, Semigroup_add a) => Numeral a where {
};

instance Semigroup_add Int where {
};

instance Numeral Int where {
};

times_num :: Num -> Num -> Num;
times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)));
times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n);
times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n));
times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n));
times_num One n = n;
times_num m One = m;

times_int :: Int -> Int -> Int;
times_int (Neg m) (Neg n) = Pos (times_num m n);
times_int (Neg m) (Pos n) = Neg (times_num m n);
times_int (Pos m) (Neg n) = Neg (times_num m n);
times_int (Pos m) (Pos n) = Pos (times_num m n);
times_int Zero_int l = Zero_int;
times_int k Zero_int = Zero_int;

class Times a where {
  times :: a -> a -> a;
};

class (One a, Times a) => Power a where {
};

instance Times Int where {
  times = times_int;
};

instance Power Int where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

instance Ab_semigroup_add Int where {
};

instance Semigroup_mult Int where {
};

instance Semiring Int where {
};

class (Times a, Zero a) => Mult_zero a where {
};

instance Mult_zero Int where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

instance Monoid_add Int where {
};

instance Comm_monoid_add Int where {
};

instance Semiring_0 Int where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

instance Monoid_mult Int where {
};

instance Semiring_numeral Int where {
};

instance Zero_neq_one Int where {
};

instance Semiring_1 Int where {
};

data Typerepa = Typerep String [Typerepa];

data Nat = Zero_nat | Suc Nat;

data Itself a = Type;

typerep_nat :: Itself Nat -> Typerepa;
typerep_nat t = Typerep "Nat.nat" [];

class Typerep a where {
  typerep :: Itself a -> Typerepa;
};

class Countable a where {
};

class (Countable a, Typerep a) => Heapa a where {
};

instance Countable Nat where {
};

instance Typerep Nat where {
  typerep = typerep_nat;
};

instance Heapa Nat where {
};

newtype Io a = IO (Heap.ST Heap.RealWorld a);

newtype Ref a = Ref Nat;

data Io_array a = IOArray (Ref a) Nat;

ref :: forall a. a -> Io (Ref a);
ref _ = error "IO.ref";

run_io :: forall a. Io a -> Heap.ST Heap.RealWorld a;
run_io (IO x) = x;

bind :: forall a b. Io a -> (a -> Io b) -> Io b;
bind x f = IO (run_io x >>= run_io . f);

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

one_nat :: Nat;
one_nat = Suc Zero_nat;

nat_of_num :: Num -> Nat;
nat_of_num (Bit1 n) = let {
                        m = nat_of_num n;
                      } in Suc (plus_nat m m);
nat_of_num (Bit0 n) = let {
                        m = nat_of_num n;
                      } in plus_nat m m;
nat_of_num One = one_nat;

nat :: Int -> Nat;
nat (Pos k) = nat_of_num k;
nat Zero_int = Zero_nat;
nat (Neg k) = Zero_nat;

returna :: forall a. a -> Io a;
returna x = IO (return x);

forMu :: forall a. [a] -> (a -> Io ()) -> Io ();
forMu [] f = returna ();
forMu (x : xs) f = bind (f x) (\ _ -> forMu xs f);

whenu :: Bool -> Io () -> Io ();
whenu cond f = (if cond then f else returna ());

lookup :: forall a. Ref a -> Io a;
lookup _ = error "IO.lookup";

update :: forall a. Ref a -> a -> Io ();
update _ _ = error "IO.update";

less_num :: Num -> Num -> Bool;
less_num (Bit1 m) (Bit0 n) = less_num m n;
less_num (Bit1 m) (Bit1 n) = less_num m n;
less_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_num (Bit0 m) (Bit0 n) = less_num m n;
less_num One (Bit1 n) = True;
less_num One (Bit0 n) = True;
less_num m One = False;

less_eq_num :: Num -> Num -> Bool;
less_eq_num (Bit1 m) (Bit0 n) = less_num m n;
less_eq_num (Bit1 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit0 n) = less_eq_num m n;
less_eq_num (Bit1 m) One = False;
less_eq_num (Bit0 m) One = False;
less_eq_num One n = True;

less_int :: Int -> Int -> Bool;
less_int (Neg k) (Neg l) = less_num l k;
less_int (Neg k) (Pos l) = True;
less_int (Neg k) Zero_int = True;
less_int (Pos k) (Neg l) = False;
less_int (Pos k) (Pos l) = less_num k l;
less_int (Pos k) Zero_int = False;
less_int Zero_int (Neg l) = False;
less_int Zero_int (Pos l) = True;
less_int Zero_int Zero_int = False;

upto_aux :: Int -> Int -> [Int] -> [Int];
upto_aux i j js =
  (if less_int j i then js else upto_aux i (minus_int j one_int) (j : js));

upto :: Int -> Int -> [Int];
upto i j = upto_aux i j [];

addr_of_ref :: forall a. Ref a -> Nat;
addr_of_ref (Ref x) = x;

get_size :: forall a. Io_array a -> Nat;
get_size (IOArray uu s) = s;

read_array :: forall a. (Heapa a) => Io_array a -> Nat -> Io a;
read_array (IOArray arr uu) i = lookup (Ref (plus_nat (addr_of_ref arr) i));

write_array :: forall a. (Heapa a) => Io_array a -> Nat -> a -> Io ();
write_array (IOArray arr uu) i val =
  update (Ref (plus_nat (addr_of_ref arr) i)) val;

swap_array :: forall a. (Heapa a) => Io_array a -> Nat -> Nat -> Io ();
swap_array arr i j =
  bind (read_array arr i)
    (\ valI ->
      bind (read_array arr j)
        (\ valJ ->
          bind (write_array arr j valI)
            (\ _ -> bind (write_array arr i valJ) (\ _ -> returna ()))));

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero_nat = False;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero_nat n = True;

of_nat_aux :: forall a. (Semiring_1 a) => (a -> a) -> Nat -> a -> a;
of_nat_aux inc Zero_nat i = i;
of_nat_aux inc (Suc n) i = of_nat_aux inc n (inc i);

of_nat :: forall a. (Semiring_1 a) => Nat -> a;
of_nat n = of_nat_aux (\ i -> plus i one) n zero;

selection_sort :: Io_array Nat -> Io ();
selection_sort arr =
  let {
    n = get_size arr;
  } in forMu (map nat (upto one_int (of_nat n)))
         (\ i ->
           bind (ref i)
             (\ min_ref ->
               bind (forMu
                      (map nat (upto (plus_int (of_nat i) one_int) (of_nat n)))
                      (\ j ->
                        bind (read_array arr j)
                          (\ valJ ->
                            bind (lookup min_ref)
                              (\ m ->
                                bind (read_array arr m)
                                  (\ valMin ->
                                    whenu (less_nat valJ valMin)
                                      (update min_ref j))))))
                 (\ _ ->
                   bind (lookup min_ref)
                     (\ m -> bind (swap_array arr i m) (\ _ -> returna ())))));

}
