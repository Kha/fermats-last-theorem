import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_apply_eq_one_of_mem_higherUnits_one_of_factorization_eq_two_of_linearMap_psCarrier_ne_zero
attribute [-instance] FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

set_option autoImplicit false

theorem CuspForm.IsNewform.apply_eq_one_of_mem_higherUnits_one_of_factorization_eq_two_of_linearMap_psCarrier_ne_zero
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime] (hM2 : M.factorization q = 2)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦ0 : Φ ≠ 0)
    (hΦg : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0) :
    ∀ u ∈ LocalNewvector.higherUnits q 1, μ₁ u = 1 ∧ μ₂ u = 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_apply_eq_one_of_mem_higherUnits_one_of_factorization_eq_two_of_linearMap_psCarrier_ne_zero.solution
