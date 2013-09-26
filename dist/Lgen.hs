module Lgen where

import qualified Prelude
import qualified Compare_dec
import qualified Datatypes
import qualified Logic
import qualified Peano_dec
import qualified Specif


data Coq_ty =
   Coq_var Datatypes.Coq_nat
 | Coq_con Datatypes.Coq_nat
 | Coq_app Coq_ty Coq_ty

ty_rect :: (Datatypes.Coq_nat -> a1) -> (Datatypes.Coq_nat -> a1) -> (Coq_ty
           -> a1 -> Coq_ty -> a1 -> a1) -> Coq_ty -> a1
ty_rect f f0 f1 t =
  case t of {
   Coq_var n -> f n;
   Coq_con n -> f0 n;
   Coq_app t0 t1 -> f1 t0 (ty_rect f f0 f1 t0) t1 (ty_rect f f0 f1 t1)}

ty_rec :: (Datatypes.Coq_nat -> a1) -> (Datatypes.Coq_nat -> a1) -> (Coq_ty
          -> a1 -> Coq_ty -> a1 -> a1) -> Coq_ty -> a1
ty_rec =
  ty_rect

eq_ty_dec :: Coq_ty -> Coq_ty -> Prelude.Bool
eq_ty_dec t t' =
  ty_rec (\n t'0 ->
    case t'0 of {
     Coq_var n0 ->
      Specif.sumbool_rec (\_ -> Logic.eq_rec_r n0 Prelude.True n) (\_ ->
        Prelude.False) (Peano_dec.eq_nat_dec n n0);
     _ -> Prelude.False}) (\n t'0 ->
    case t'0 of {
     Coq_con n0 ->
      Specif.sumbool_rec (\_ -> Logic.eq_rec_r n0 Prelude.True n) (\_ ->
        Prelude.False) (Peano_dec.eq_nat_dec n n0);
     _ -> Prelude.False}) (\t0 h t1 h0 t'0 ->
    case t'0 of {
     Coq_app t2 t3 ->
      Specif.sumbool_rec (\_ ->
        Logic.eq_rec_r t2
          (Specif.sumbool_rec (\_ -> Logic.eq_rec_r t3 Prelude.True t1)
            (\_ -> Prelude.False) (h0 t3)) t0) (\_ -> Prelude.False) 
        (h t2);
     _ -> Prelude.False}) t t'

fv :: Coq_ty -> Datatypes.Coq_list Datatypes.Coq_nat
fv t =
  case t of {
   Coq_var n -> Datatypes.Coq_cons n Datatypes.Coq_nil;
   Coq_con n -> Datatypes.Coq_nil;
   Coq_app l r -> Datatypes.app (fv l) (fv r)}

max_list :: (Datatypes.Coq_list Datatypes.Coq_nat) -> Datatypes.Coq_nat
max_list l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.O;
   Datatypes.Coq_cons x l' ->
    let {filtered_var = Specif.proj1_sig (max_list l')} in
    let {filtered_var0 = Compare_dec.le_gt_dec x filtered_var} in
    case filtered_var0 of {
     Prelude.True -> Datatypes.S filtered_var;
     Prelude.False -> Datatypes.S x}}

type Coq_gen_list =
  Datatypes.Coq_list
  (Datatypes.Coq_prod (Datatypes.Coq_prod Coq_ty Coq_ty) Datatypes.Coq_nat)

lookup_gen_list :: Coq_ty -> Coq_ty -> Coq_gen_list -> Prelude.Maybe
                   Datatypes.Coq_nat
lookup_gen_list t t' l =
  case l of {
   Datatypes.Coq_nil -> Prelude.Nothing;
   Datatypes.Coq_cons x l' ->
    case x of {
     Datatypes.Coq_pair p c ->
      case p of {
       Datatypes.Coq_pair a b ->
        let {filtered_var = eq_ty_dec t a} in
        let {filtered_var0 = eq_ty_dec b t'} in
        case filtered_var of {
         Prelude.True ->
          case filtered_var0 of {
           Prelude.True -> Prelude.Just c;
           Prelude.False ->
            let {filtered_var1 = lookup_gen_list t t' l'} in
            case filtered_var1 of {
             Prelude.Just x0 -> Prelude.Just (Specif.proj1_sig x0);
             Prelude.Nothing -> Prelude.Nothing}};
         Prelude.False ->
          case filtered_var0 of {
           Prelude.True ->
            let {filtered_var1 = lookup_gen_list t t' l'} in
            case filtered_var1 of {
             Prelude.Just x0 -> Prelude.Just (Specif.proj1_sig x0);
             Prelude.Nothing -> Prelude.Nothing};
           Prelude.False ->
            let {filtered_var1 = lookup_gen_list t t' l'} in
            case filtered_var1 of {
             Prelude.Just x0 -> Prelude.Just (Specif.proj1_sig x0);
             Prelude.Nothing -> Prelude.Nothing}}}}}}

lgen_aux :: Coq_ty -> Coq_ty -> Coq_gen_list -> Datatypes.Coq_nat ->
            (Datatypes.Coq_prod Coq_ty
            (Datatypes.Coq_prod Coq_gen_list Datatypes.Coq_nat))
lgen_aux t t' l m =
  case t of {
   Coq_var n ->
    case lookup_gen_list t t' l of {
     Prelude.Just s -> Datatypes.Coq_pair (Coq_var s) (Datatypes.Coq_pair l
      m);
     Prelude.Nothing -> Datatypes.Coq_pair (Coq_var m) (Datatypes.Coq_pair
      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair t t') m) l)
      (Datatypes.S m))};
   Coq_con n ->
    case t' of {
     Coq_con n' ->
      case Peano_dec.eq_nat_dec n n' of {
       Prelude.True -> Datatypes.Coq_pair (Coq_con n) (Datatypes.Coq_pair l
        m);
       Prelude.False ->
        case lookup_gen_list t t' l of {
         Prelude.Just s -> Datatypes.Coq_pair (Coq_var s) (Datatypes.Coq_pair
          l m);
         Prelude.Nothing -> Datatypes.Coq_pair (Coq_var m)
          (Datatypes.Coq_pair (Datatypes.Coq_cons (Datatypes.Coq_pair
          (Datatypes.Coq_pair (Coq_con n) (Coq_con n')) m) l) (Datatypes.S
          m))}};
     _ ->
      case lookup_gen_list t t' l of {
       Prelude.Just s -> Datatypes.Coq_pair (Coq_var s) (Datatypes.Coq_pair l
        m);
       Prelude.Nothing -> Datatypes.Coq_pair (Coq_var m) (Datatypes.Coq_pair
        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair t t') m)
        l) (Datatypes.S m))}};
   Coq_app f r ->
    case t' of {
     Coq_app f' r' ->
      let {v = lgen_aux f f' l m} in
      let {
       v' = lgen_aux r r' (Datatypes.fst (Datatypes.snd v))
              (Datatypes.snd (Datatypes.snd v))}
      in
      Datatypes.Coq_pair (Coq_app (Datatypes.fst v) (Datatypes.fst v'))
      (Datatypes.Coq_pair (Datatypes.fst (Datatypes.snd v'))
      (Datatypes.snd (Datatypes.snd v')));
     _ ->
      case lookup_gen_list t t' l of {
       Prelude.Just s -> Datatypes.Coq_pair (Coq_var s) (Datatypes.Coq_pair l
        m);
       Prelude.Nothing -> Datatypes.Coq_pair (Coq_var m) (Datatypes.Coq_pair
        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair t t') m)
        l) (Datatypes.S m))}}}

lgen :: Coq_ty -> Coq_ty -> Coq_ty
lgen t t' =
  let {s = max_list (Datatypes.app (fv t) (fv t'))} in
  let {s0 = lgen_aux t t' Datatypes.Coq_nil s} in
  case s0 of {
   Datatypes.Coq_pair t1 p -> t1}

lcg :: (Datatypes.Coq_list Coq_ty) -> Prelude.Maybe Coq_ty
lcg l =
  case l of {
   Datatypes.Coq_nil -> Prelude.Nothing;
   Datatypes.Coq_cons x l' ->
    case lcg l' of {
     Prelude.Just s -> Prelude.Just (lgen x s);
     Prelude.Nothing -> Prelude.Just x}}

tint :: Coq_ty
tint =
  Coq_con (Datatypes.S Datatypes.O)

tfloat :: Coq_ty
tfloat =
  Coq_con (Datatypes.S (Datatypes.S Datatypes.O))

