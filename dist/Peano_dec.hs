module Peano_dec where

import qualified Prelude
import qualified Datatypes
import qualified Specif


coq_O_or_S :: Datatypes.Coq_nat -> Prelude.Maybe Datatypes.Coq_nat
coq_O_or_S n =
  Datatypes.nat_rec Prelude.Nothing (\n0 iHn -> Prelude.Just n0) n

eq_nat_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
eq_nat_dec n =
  Datatypes.nat_rec (\m ->
    case m of {
     Datatypes.O -> Prelude.True;
     Datatypes.S m0 -> Prelude.False}) (\n0 iHn m ->
    case m of {
     Datatypes.O -> Prelude.False;
     Datatypes.S m0 ->
      Specif.sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (iHn m0)})
    n

