module Compare_dec where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Specif


zerop :: Datatypes.Coq_nat -> Prelude.Bool
zerop n =
  case n of {
   Datatypes.O -> Prelude.True;
   Datatypes.S n0 -> Prelude.False}

lt_eq_lt_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Maybe
                Prelude.Bool
lt_eq_lt_dec n m =
  Datatypes.nat_rec (\m0 ->
    case m0 of {
     Datatypes.O -> Prelude.Just Prelude.False;
     Datatypes.S m1 -> Prelude.Just Prelude.True}) (\n0 iHn m0 ->
    case m0 of {
     Datatypes.O -> Prelude.Nothing;
     Datatypes.S m1 -> iHn m1}) n m

gt_eq_gt_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Maybe
                Prelude.Bool
gt_eq_gt_dec n m =
  lt_eq_lt_dec n m

le_lt_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
le_lt_dec n m =
  Datatypes.nat_rec (\m0 -> Prelude.True) (\n0 iHn m0 ->
    case m0 of {
     Datatypes.O -> Prelude.False;
     Datatypes.S m1 ->
      Specif.sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (iHn m1)})
    n m

le_le_S_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
le_le_S_dec n m =
  le_lt_dec n m

le_ge_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
le_ge_dec n m =
  Specif.sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
    (le_lt_dec n m)

le_gt_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
le_gt_dec n m =
  le_lt_dec n m

le_lt_eq_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
le_lt_eq_dec n m =
  let {s = lt_eq_lt_dec n m} in
  case s of {
   Prelude.Just s0 -> s0;
   Prelude.Nothing -> Logic.coq_False_rec}

le_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
le_dec n m =
  le_gt_dec n m

lt_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
lt_dec n m =
  le_dec (Datatypes.S n) m

gt_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
gt_dec n m =
  lt_dec m n

ge_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
ge_dec n m =
  le_dec m n

nat_compare :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
               Datatypes.Coq_comparison
nat_compare n m =
  case n of {
   Datatypes.O ->
    case m of {
     Datatypes.O -> Datatypes.Eq;
     Datatypes.S n0 -> Datatypes.Lt};
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.Gt;
     Datatypes.S m' -> nat_compare n' m'}}

nat_compare_alt :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                   Datatypes.Coq_comparison
nat_compare_alt n m =
  case lt_eq_lt_dec n m of {
   Prelude.Just s ->
    case s of {
     Prelude.True -> Datatypes.Lt;
     Prelude.False -> Datatypes.Eq};
   Prelude.Nothing -> Datatypes.Gt}

leb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
leb m x =
  case m of {
   Datatypes.O -> Datatypes.Coq_true;
   Datatypes.S m' ->
    case x of {
     Datatypes.O -> Datatypes.Coq_false;
     Datatypes.S n' -> leb m' n'}}

