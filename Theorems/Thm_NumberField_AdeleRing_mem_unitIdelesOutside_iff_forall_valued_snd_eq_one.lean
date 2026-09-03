import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_mem_unitIdelesOutside_iff_forall_valued_snd_eq_one

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

theorem NumberField.AdeleRing.mem_unitIdelesOutside_iff_forall_valued_snd_eq_one
    (K : Type) [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K))) (x : (AdeleRing (𝓞 K) K)ˣ) :
    x ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K T ↔
      ∀ w : HeightOneSpectrum (𝓞 K), w ∉ T →
        Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_mem_unitIdelesOutside_iff_forall_valued_snd_eq_one.solution
