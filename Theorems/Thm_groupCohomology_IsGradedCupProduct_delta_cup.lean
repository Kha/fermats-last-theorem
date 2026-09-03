import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import P2M.Util
import P2M.Sol.S_groupCohomology_IsGradedCupProduct_delta_cup

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory groupCohomology
theorem groupCohomology.IsGradedCupProduct.delta_cup {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (B : Rep.{u} k G)
    (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact)
    (cup₁ : groupCohomology.GradedCupFamily X.X₁ B) (h₁ : groupCohomology.IsGradedCupProduct X.X₁ B cup₁)
    (cup₃ : groupCohomology.GradedCupFamily X.X₃ B) (h₃ : groupCohomology.IsGradedCupProduct X.X₃ B cup₃)
    (p q : ℕ) (x : groupCohomology X.X₃ p) (y : groupCohomology B q) :
    (groupCohomology.δ hXB (p + q) (p + 1 + q) (by omega)).hom (cup₃ p q x y)
      = cup₁ (p + 1) q ((groupCohomology.δ hX p (p + 1) rfl).hom x) y := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_IsGradedCupProduct_delta_cup.solution
