import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_GenuineDescent_unitsMap_beta_mem_principalIdeles_iff

set_option autoImplicit false
open NumberField M4aHerbrand M4aHerbrand.GenuineDescent

theorem M4aHerbrand.GenuineDescent.unitsMap_beta_mem_principalIdeles_iff
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (x : (AdeleRing (𝓞 E) E)ˣ) :
    Units.map (genuineBaseChange E F).β.toMonoidHom x ∈ principalIdeles (𝓞 F) F ↔
      x ∈ principalIdeles (𝓞 E) E := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_GenuineDescent_unitsMap_beta_mem_principalIdeles_iff.solution
