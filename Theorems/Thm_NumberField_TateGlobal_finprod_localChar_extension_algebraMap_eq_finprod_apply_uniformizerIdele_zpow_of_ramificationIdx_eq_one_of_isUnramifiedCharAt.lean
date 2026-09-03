import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_finprod_localChar_extension_algebraMap_eq_finprod_apply_uniformizerIdele_zpow_of_ramificationIdx_eq_one_of_isUnramifiedCharAt

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm

theorem NumberField.TateGlobal.finprod_localChar_extension_algebraMap_eq_finprod_apply_uniformizerIdele_zpow_of_ramificationIdx_eq_one_of_isUnramifiedCharAt
    (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [Algebra E K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 E))
    (he : ∀ w : v.Extension (𝓞 K), Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1)
    (hμ : ∀ w : v.Extension (𝓞 K), IsUnramifiedCharAt μ w.1)
    (x : (v.adicCompletion E)ˣ) (n : ℤ)
    (hx : Valued.v (x : v.adicCompletion E) = WithZero.exp n) :
    (∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
        (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion K)).toMonoidHom x) : ℂˣ) : ℂ)) =
      (∏ᶠ w : v.Extension (𝓞 K), ((μ (uniformizerIdele K w.1) : ℂˣ) : ℂ)) ^ (-n) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_finprod_localChar_extension_algebraMap_eq_finprod_apply_uniformizerIdele_zpow_of_ramificationIdx_eq_one_of_isUnramifiedCharAt.solution
