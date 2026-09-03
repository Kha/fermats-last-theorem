import Mathlib
import Definitions.Def_GroupCohomology_SplittingModule
import P2M.Util
import P2M.Sol.S_Rep_splittingShortComplex_shortExact

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.splittingShortComplex_shortExact {k G : Type u} [CommRing k] [Group G]
    (C : Rep.{u} k G) (φ : groupCohomology.cocycles₂ C) :
    (Rep.splittingShortComplex C φ).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_splittingShortComplex_shortExact.solution
