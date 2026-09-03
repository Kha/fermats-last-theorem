import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct

theorem TwistedUnipotentTerm.semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (hξv : ∀ ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = 1)
    (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ =
      ∏ᶠ w : v.Extension (𝓞 L),
        ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          (-WithZero.log (Valued.v
            ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : (w.1.adicCompletion L)ˣ) :
              w.1.adicCompletion L))) := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits.solution
