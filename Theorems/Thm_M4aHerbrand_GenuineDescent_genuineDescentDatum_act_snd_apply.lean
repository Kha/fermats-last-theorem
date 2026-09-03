import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply

set_option autoImplicit false
open scoped NumberField.PlaceTransport
theorem M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers L) L)
    {w w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)} (h : σ • w = w') :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).2 w'
      = NumberField.PlaceTransport.transport σ h (x.2 w) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply.solution
