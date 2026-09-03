import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_Ideal_iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem Ideal.iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite
    (S : Type*) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (C : Type*) [CommRing C] [Algebra S C] [Module.Finite S C] [Nontrivial C] :
    ⨅ n : ℕ, (maximalIdeal S ^ n).map (algebraMap S C) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Ideal_iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite.solution
