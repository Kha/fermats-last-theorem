import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_GluedPic0
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F]
    {ι : Type*} [Fintype ι]
    (E₁ E₂ : Divisor k F)
    [FiniteDimensional k ↥(riemannRochSpace E₁)] [FiniteDimensional k ↥(riemannRochSpace E₂)]
    (v₁ v₂ : ι → Place k F) (t₁ t₂ : ι → F)
    (ht₁ : ∀ i, t₁ i ≠ 0 ∧ (v₁ i).ord (t₁ i) = E₁ (v₁ i))
    (ht₂ : ∀ i, t₂ i ≠ 0 ∧ (v₂ i).ord (t₂ i) = E₂ (v₂ i))
    (lam : ι → k)
    (hsurj : ∀ c : ι → k, ∃ p ∈ riemannRochSpace E₁, ∀ i, (v₁ i).HasValue (t₁ i * p) (c i))
    (T : Submodule k (F × F))
    (hT : ∀ p, p ∈ T ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : k, (v₁ i).HasValue (t₁ i * p.1) (lam i * c) ∧ (v₂ i).HasValue (t₂ i * p.2) c) :
    FiniteDimensional k ↥T ∧
      Module.finrank k ↥T + Fintype.card ι ≤
        Module.finrank k ↥(riemannRochSpace E₁) + Module.finrank k ↥(riemannRochSpace E₂) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul.solution
