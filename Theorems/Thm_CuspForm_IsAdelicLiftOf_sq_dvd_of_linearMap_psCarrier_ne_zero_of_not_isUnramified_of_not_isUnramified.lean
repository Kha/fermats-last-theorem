import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_sq_dvd_of_linearMap_psCarrier_ne_zero_of_not_isUnramified_of_not_isUnramified
attribute [-instance] FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.sq_dvd_of_linearMap_psCarrier_ne_zero_of_not_isUnramified_of_not_isUnramified
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (_hlift : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (_hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v) (_hf0 : f ≠ 0)
    (_hμ₁ : ¬ LocalNewvector.IsUnramified q μ₁) (_hμ₂ : ¬ LocalNewvector.IsUnramified q μ₂) :
    q ^ 2 ∣ M := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_sq_dvd_of_linearMap_psCarrier_ne_zero_of_not_isUnramified_of_not_isUnramified.solution
