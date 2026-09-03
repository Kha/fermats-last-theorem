import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_Bridge_genuineBeta_comp_of_tower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField M4aHerbrand.Bridge

theorem M4aHerbrand.Bridge.genuineBeta_comp_of_tower
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K''] :
    (genuineβ K' K'').comp (genuineβ K K') = genuineβ K K'' := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_Bridge_genuineBeta_comp_of_tower.solution
