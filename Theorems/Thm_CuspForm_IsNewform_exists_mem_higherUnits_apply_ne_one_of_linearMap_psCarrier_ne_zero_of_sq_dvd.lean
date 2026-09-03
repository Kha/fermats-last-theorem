import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_exists_mem_higherUnits_apply_ne_one_of_linearMap_psCarrier_ne_zero_of_sq_dvd
attribute [-instance] FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

set_option autoImplicit false

theorem CuspForm.IsNewform.exists_mem_higherUnits_apply_ne_one_of_linearMap_psCarrier_ne_zero_of_sq_dvd
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime] (hqM : q ^ 2 ∣ M)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΦg : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hne : f ≠ 0) :
    ∃ u ∈ LocalNewvector.higherUnits q 0, μ₁ u ≠ 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_exists_mem_higherUnits_apply_ne_one_of_linearMap_psCarrier_ne_zero_of_sq_dvd.solution
