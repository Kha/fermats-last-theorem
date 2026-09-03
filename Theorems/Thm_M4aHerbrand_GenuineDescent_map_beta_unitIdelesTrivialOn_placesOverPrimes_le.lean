import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_GenuineDescent_map_beta_unitIdelesTrivialOn_placesOverPrimes_le

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent

theorem M4aHerbrand.GenuineDescent.map_beta_unitIdelesTrivialOn_placesOverPrimes_le
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] (S : Set Nat.Primes) :
    (unitIdelesTrivialOn (𝓞 E) E (NumberField.placesOverPrimes E S)).map
        (Units.map ((genuineBaseChange E F).β : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 F) F).toMonoidHom)
      ≤ unitIdelesTrivialOn (𝓞 F) F (NumberField.placesOverPrimes F S) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_GenuineDescent_map_beta_unitIdelesTrivialOn_placesOverPrimes_le.solution
