import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ConductorDatum
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_exists_mem_span_fixed_gl2CongruenceSubgroup_of_fixedSubmodule_gl2CongruenceSubgroup_ne_bot
attribute [-instance] LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.exists_mem_span_fixed_gl2CongruenceSubgroup_of_fixedSubmodule_gl2CongruenceSubgroup_ne_bot
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] (n : ℕ)
    (hfix : LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q n) (LocalNewvector.AdelicSpan Φ) ≠ ⊥) :
    ∃ y : LocalNewvector.AdelicSpan Φ,
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ) ∧
      y ≠ 0 ∧
      y ∈ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q n) (LocalNewvector.AdelicSpan Φ) ∧
      ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • y = y := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_exists_mem_span_fixed_gl2CongruenceSubgroup_of_fixedSubmodule_gl2CongruenceSubgroup_ne_bot.solution
