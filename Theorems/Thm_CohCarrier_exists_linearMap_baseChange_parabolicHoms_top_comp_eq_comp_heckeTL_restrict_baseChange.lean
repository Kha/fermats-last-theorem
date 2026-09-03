import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

open scoped TensorProduct

theorem CohCarrier.exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange
    (N : ℕ) [NeZero N] (K : Type) [Field K] [CharZero K] (Ω : Type) [Field Ω] [Algebra K Ω] :
    ∃ (hpar : ∀ (p : ℕ) (hp : p.Prime) (w : CohCarrier.H1 N ⊤ K),
        w ∈ ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K →
          (haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ K p) w ∈
            ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K)
      (Φ : Ω ⊗[K] ↥(ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K) →ₗ[Ω]
        CohCarrier.H1 N ⊤ Ω),
      (∀ (p p' : ℕ) (hp : p.Prime) (hp' : p'.Prime),
        Commute ((haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ K p).restrict (hpar p hp))
          ((haveI : NeZero p' := ⟨hp'.ne_zero⟩; CohCarrier.heckeTL N ⊤ K p').restrict (hpar p' hp'))) ∧
      Function.Injective Φ ∧
      LinearMap.range Φ = ModularCurve.Period.parabolicHoms Ω (CohCarrier.GammaH N ⊤) Ω ∧
      ∀ (p : ℕ) (hp : p.Prime),
        (haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ Ω p) ∘ₗ Φ =
          Φ ∘ₗ ((haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ K p).restrict (hpar p hp)).baseChange Ω := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange.solution
