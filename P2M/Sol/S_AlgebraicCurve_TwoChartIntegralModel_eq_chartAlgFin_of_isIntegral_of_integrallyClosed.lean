import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_eq_chartAlgFin_of_isIntegral_of_integrallyClosed

set_option autoImplicit false

open AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (B : Subalgebra R F) (hj : j ∈ B)
    (hint : ∀ x ∈ B, IsIntegral (Algebra.adjoin R ({j} : Set F)) x)
    (hic : ∀ x : F, IsIntegral B x → x ∈ B) :
    B = chartAlgFin R F j := by
  apply le_antisymm
  · intro x hx
    exact (mem_chartAlg_iff R F).mpr (hint x hx)
  · intro x hx
    have hx' : IsIntegral (Algebra.adjoin R ({j} : Set F)) x := (mem_chartAlg_iff R F).mp hx
    have hle : Algebra.adjoin R ({j} : Set F) ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hj)
    exact hic x (hx'.map_of_comp_eq (Subalgebra.inclusion hle).toRingHom (RingHom.id F) (by ext; rfl))
