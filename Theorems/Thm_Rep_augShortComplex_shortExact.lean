import Mathlib
import Definitions.Def_GroupCohomology_SplittingModule
import P2M.Util
import P2M.Sol.S_Rep_augShortComplex_shortExact

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.augShortComplex_shortExact (k G : Type u) [CommRing k] [Group G] :
    (Rep.augShortComplex k G).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_augShortComplex_shortExact.solution
