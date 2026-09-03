import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_CuspForm_span_tmul_intTwoCuspReduce_eq_top

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.span_tmul_intTwoCuspReduce_eq_top
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (K : Type*) [Field K] [Algebra (ZMod p) K] :
    Submodule.span K {x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)),
          x = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_span_tmul_intTwoCuspReduce_eq_top.solution
