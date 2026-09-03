import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isIso_of_isFinite_of_finrank_closedPoint_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (K : Type) [Field K] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of K)) [IsFinite p]
    (h : p.finrank (IsLocalRing.closedPoint K) = 1) :
    IsIso p := by
  refine (Scheme.Hom.isIso_iff_finrank_eq p).mpr ?_
  funext s
  have hs : s = IsLocalRing.closedPoint K := by
    apply PrimeSpectrum.ext
    rw [Ideal.eq_bot_of_prime s.asIdeal]
    exact (Ideal.eq_bot_of_prime _).symm
  rw [hs, h]
  rfl
