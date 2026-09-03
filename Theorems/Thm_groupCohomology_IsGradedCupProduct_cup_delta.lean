import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import P2M.Util
import P2M.Sol.S_groupCohomology_IsGradedCupProduct_cup_delta

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory groupCohomology
theorem groupCohomology.IsGradedCupProduct.cup_delta {k G : Type u} [CommRing k] [Group G]
    (A : Rep.{u} k G) {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (cup₁ : groupCohomology.GradedCupFamily A X.X₁) (h₁ : groupCohomology.IsGradedCupProduct A X.X₁ cup₁)
    (cup₃ : groupCohomology.GradedCupFamily A X.X₃) (h₃ : groupCohomology.IsGradedCupProduct A X.X₃ cup₃)
    (p q : ℕ) (x : groupCohomology A p) (y : groupCohomology X.X₃ q) :
    (groupCohomology.δ hAX (p + q) (p + q + 1) rfl).hom (cup₃ p q x y)
      = ((-1 : k) ^ p) • cup₁ p (q + 1) x ((groupCohomology.δ hX q (q + 1) rfl).hom y) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_IsGradedCupProduct_cup_delta.solution
