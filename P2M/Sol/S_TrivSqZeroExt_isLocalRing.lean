import Mathlib
import P2M.Util
namespace P2MW.S_TrivSqZeroExt_isLocalRing

set_option autoImplicit false

open TrivSqZeroExt DualNumber

theorem solution {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [IsLocalRing R] : IsLocalRing (TrivSqZeroExt R M) := by
  haveI : Nontrivial (TrivSqZeroExt R M) := (TrivSqZeroExt.inl_injective (R := R) (M := M)).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst with h | h
  · exact Or.inl (isUnit_iff_isUnit_fst.2 h)
  · refine Or.inr (isUnit_iff_isUnit_fst.2 ?_)
    rwa [fst_sub, fst_one]
