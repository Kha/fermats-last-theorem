import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_IsLocalRing_exists_isDiscreteValuationRing_ringHom_of_finite_residueField
import P2M.Util
namespace P2MW.S_IsLocalRing_exists_isDiscreteValuationRing_ringHom_comp_eq_of_pow_sub_one_eq_mul_natCast
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing FormalGroup

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Finite (ResidueField R)] (hchar : CharP (ResidueField R) q)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (ε : A) (hε : IsUnit ε) (hϖq : ϖ ^ (q - 1) = ε * (q : A))
    (ι : A →+* R) [IsLocalHom ι] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (σ : A →+* W) (_ : maximalIdeal W = Ideal.span {σ ϖ})
      (g : W →+* R) (_ : IsLocalHom g),
      g.comp σ = ι ∧ ∀ r : R, ∃ w : W, r - g w ∈ maximalIdeal R := by
  letI : Algebra A R := ι.toAlgebra
  haveI : IsLocalHom (algebraMap A R) := ‹IsLocalHom ι›
  obtain ⟨W, iW1, iW2, iW3, iW4, σ, hσ, τ, hτ, hsurj, hcomp⟩ :=
    IsLocalRing.exists_isDiscreteValuationRing_ringHom_of_finite_residueField A ϖ hϖ R
  refine ⟨W, iW1, iW2, iW3, iW4, σ, hσ, τ, hτ, hcomp, fun r => ?_⟩
  obtain ⟨w, hw⟩ := hsurj (residue R r)
  refine ⟨w, ?_⟩
  rw [RingHom.comp_apply] at hw
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact hw.symm
