import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap

set_option autoImplicit false

open NumberField M4aHerbrand.GenuineDescent

theorem M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (m : M) :
    (genuineBaseChange K M).adelicNorm (algebraMap M (AdeleRing (𝓞 M) M) m) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K m) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap.solution
