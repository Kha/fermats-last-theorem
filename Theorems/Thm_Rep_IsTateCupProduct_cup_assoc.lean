import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import P2M.Util
import P2M.Sol.S_Rep_IsTateCupProduct_cup_assoc

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.IsTateCupProduct.cup_assoc {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B C : Rep.{u} k G)
    (p q r r₁₂ r₂₃ r₁₂₃ : ℤ) (h₁₂ : p + q = r₁₂) (h₂₃ : q + r = r₂₃) (h : r₁₂ + r = r₁₂₃)
    (x : A.tateCohomology p) (y : B.tateCohomology q) (z : C.tateCohomology r) :
    cup (A ⊗ B) C r₁₂ r r₁₂₃ h (cup A B p q r₁₂ h₁₂ x y) z
      = (Rep.tateMap (α_ A B C).inv r₁₂₃).hom (cup A (B ⊗ C) p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_IsTateCupProduct_cup_assoc.solution
