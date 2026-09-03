import Definitions.Def_NumberField_IdeleProductMeasure
import P2M.Util
import P2M.Sol.S_NumberField_Idele_norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.Idele.norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (u : Kˣ) :
    ‖algebraMap K (v.adicCompletion K) (u : K)‖ =
      ‖(ϖ : v.adicCompletion K)‖ ^
        NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord.solution
