import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_finite_setOf_valued_snd_ne_one

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

theorem NumberField.AdeleRing.finite_setOf_valued_snd_ne_one
    (K : Type) [Field K] [NumberField K] (x : (AdeleRing (𝓞 K) K)ˣ) :
    {w : HeightOneSpectrum (𝓞 K) | Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) ≠ 1}.Finite := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_finite_setOf_valued_snd_ne_one.solution
