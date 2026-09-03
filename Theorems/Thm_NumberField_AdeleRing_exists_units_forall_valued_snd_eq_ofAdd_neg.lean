import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_exists_units_forall_valued_snd_eq_ofAdd_neg

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

theorem NumberField.AdeleRing.exists_units_forall_valued_snd_eq_ofAdd_neg
    (K : Type) [Field K] [NumberField K] (m : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    ∃ q : (AdeleRing (𝓞 K) K)ˣ, ∀ w : HeightOneSpectrum (𝓞 K),
      Valued.v (((q : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) =
        ((Multiplicative.ofAdd (-(m w)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_exists_units_forall_valued_snd_eq_ofAdd_neg.solution
