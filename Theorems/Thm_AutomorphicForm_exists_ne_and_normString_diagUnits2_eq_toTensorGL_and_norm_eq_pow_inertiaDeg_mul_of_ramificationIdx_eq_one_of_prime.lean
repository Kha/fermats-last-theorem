import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1)
    (w : v.Extension (𝓞 L))
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (e₁ e₂ : ℕ) :
    ∃ (a b : (v.adicCompletion K)ˣ) (α β : (L ⊗[K] v.adicCompletion K)ˣ),
      a ≠ b ∧
      normString K L (v.adicCompletion K) σ (diagUnits2 α β) = toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) ∧
      ‖((a : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
        ‖((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K)‖ ^ (v.asIdeal.inertiaDeg' w.1.asIdeal * e₁) ∧
      ‖((b : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
        ‖((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K)‖ ^ (v.asIdeal.inertiaDeg' w.1.asIdeal * e₂) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime.solution
