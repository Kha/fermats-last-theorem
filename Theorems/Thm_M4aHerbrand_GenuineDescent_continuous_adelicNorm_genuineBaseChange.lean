import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange

set_option autoImplicit false

open NumberField M4aHerbrand.GenuineDescent

theorem M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] :
    Continuous (genuineBaseChange K M).adelicNorm := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange.solution
