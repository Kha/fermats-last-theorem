import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_GenuineDescent_isClosedEmbedding_unitsMap_genuineBaseChange

set_option autoImplicit false

open NumberField

theorem M4aHerbrand.GenuineDescent.isClosedEmbedding_unitsMap_genuineBaseChange
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Topology.IsClosedEmbedding
      (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom :
        (AdeleRing (𝓞 K) K)ˣ → (AdeleRing (𝓞 L) L)ˣ) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_GenuineDescent_isClosedEmbedding_unitsMap_genuineBaseChange.solution
