import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_IdeleBox
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.AdeleRing.isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Ca : Set (InfiniteAdeleRing K)ˣ) (hCa : IsCompact Ca)
    (Cf : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K))
    (hCf : ∀ v ∈ S, IsCompact (Cf v)) (hCf0 : ∀ v ∈ S, (0 : v.adicCompletion K) ∉ Cf v) :
    IsCompact ({z : (AdeleRing (𝓞 K) K)ˣ |
        Units.map (AdelicLevel.adeleArch (𝓞 K) K) z ∈ Ca ∧
        ∀ v ∈ S, (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ Cf v} ∩
      ↑(NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside.solution
