import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_IsInfReductionMap_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero

set_option autoImplicit false

open scoped TensorProduct ModularForm MatrixGroups

theorem ModularCurve.IsInfReductionMap.mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (W : ModularForm.AtkinLehnerDatum M p)
    (K : Type*) [Field K] [Algebra (ZMod p) K]
    {ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hρ : ModularCurve.IsInfReductionMap K p M H hpM ρ)
    (x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p) (hx : ρ x = 0) :
    x ∈ Submodule.span K {z : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p |
      ∃ y : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)),
        (∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑(y : CuspForm (CohCarrier.GammaH M H) 2)) n = (p : ℂ) * m) ∧
        z = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsInfReductionMap_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero.solution
