import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isLocallyConstant_and_hasCompactSupport_indicator_prod_semiLocalEval

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.isLocallyConstant_and_hasCompactSupport_indicator_prod_semiLocalEval
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sx : Finset (HeightOneSpectrum (𝓞 K)))
    (Fv : (v : HeightOneSpectrum (𝓞 K)) → L ⊗[K] v.adicCompletion K → ℂ)
    (hFv : ∀ v ∈ Sx, IsLocallyConstant (Fv v) ∧ HasCompactSupport (Fv v)) :
    IsLocallyConstant (fun xf : FiniteAdeleRing (𝓞 L) L =>
        {xf : FiniteAdeleRing (𝓞 L) L | ∀ v ∉ Sx,
            AutomorphicForm.semiLocalEval K L v xf ∈ AutomorphicForm.semiLocalIntegers K L v}.indicator
          (fun xf => ∏ v ∈ Sx, Fv v (AutomorphicForm.semiLocalEval K L v xf)) xf) ∧
      HasCompactSupport (fun xf : FiniteAdeleRing (𝓞 L) L =>
        {xf : FiniteAdeleRing (𝓞 L) L | ∀ v ∉ Sx,
            AutomorphicForm.semiLocalEval K L v xf ∈ AutomorphicForm.semiLocalIntegers K L v}.indicator
          (fun xf => ∏ v ∈ Sx, Fv v (AutomorphicForm.semiLocalEval K L v xf)) xf) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isLocallyConstant_and_hasCompactSupport_indicator_prod_semiLocalEval.solution
