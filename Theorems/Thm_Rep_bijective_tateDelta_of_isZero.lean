import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import P2M.Util
import P2M.Sol.S_Rep_bijective_tateDelta_of_isZero

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.bijective_tateDelta_of_isZero {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ)
    (h₀ : CategoryTheory.Limits.IsZero (X.X₂.tateCohomology n))
    (h₁ : CategoryTheory.Limits.IsZero (X.X₂.tateCohomology (n + 1))) :
    Function.Bijective (Rep.tateδ hX n).hom := by p2m_exact_reverting @_root_.P2MW.S_Rep_bijective_tateDelta_of_isZero.solution
