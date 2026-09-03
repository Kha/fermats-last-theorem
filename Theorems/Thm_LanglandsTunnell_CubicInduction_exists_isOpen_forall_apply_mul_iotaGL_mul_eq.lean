import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse
open scoped nonZeroDivisors

theorem
LanglandsTunnell.CubicInduction.exists_isOpen_forall_apply_mul_iotaGL_mul_eq
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (W : LocalGL3 v → ℂ)
    (hW : ∃ (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)), W = coefficientFn Λ f)
    (b : ℕ) (g₃ : LocalGL3 v) (k₀ : GL (Fin 2) (v.adicCompletion ℚ)) :
    ∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b), ∀ k' ∈ U, ∀ x : LocalGL3 v,
        W (x * k' * (iotaGL (k₀ * k) * g₃)) = W (x * (iotaGL (k₀ * k) * g₃)) ∧
        W (x * k' * (iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃)) =
          W (x * (iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq.solution
