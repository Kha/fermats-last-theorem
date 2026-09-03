import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_exists_linearMap_psCarrier_of_gl2ReductionRep_unipotent_fixed_ne_zero
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

set_option autoImplicit false

theorem CuspForm.IsNewform.exists_linearMap_psCarrier_of_gl2ReductionRep_unipotent_fixed_ne_zero
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hg : g.IsNewform) (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hgΦ : g.IsAdelicLiftOf Φ)
    (y : LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) (LocalNewvector.AdelicSpan Φ))
    (hy0 : y ≠ 0)
    (hN : ∀ t : ZMod q,
      LocalNewvector.gl2ReductionRep q (LocalNewvector.AdelicSpan Φ) (CuspidalType.unipotent q t) y = y) :
    ∃ (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂),
      (∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v) ∧ f ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_exists_linearMap_psCarrier_of_gl2ReductionRep_unipotent_fixed_ne_zero.solution
