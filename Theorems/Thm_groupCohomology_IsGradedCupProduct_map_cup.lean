import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import P2M.Util
import P2M.Sol.S_groupCohomology_IsGradedCupProduct_map_cup

set_option autoImplicit false
set_option maxHeartbeats 600000
universe u
open CategoryTheory MonoidalCategory groupCohomology
theorem groupCohomology.IsGradedCupProduct.map_cup {k G H : Type u} [CommRing k] [Group G] [Group H]
    (f : H →* G) {A B : Rep.{u} k G} {A' B' : Rep.{u} k H} (φ : Rep.res f A ⟶ A') (ψ : Rep.res f B ⟶ B')
    (cup : groupCohomology.GradedCupFamily A B) (hcup : groupCohomology.IsGradedCupProduct A B cup)
    (cup' : groupCohomology.GradedCupFamily A' B') (hcup' : groupCohomology.IsGradedCupProduct A' B' cup')
    (p q : ℕ) (x : groupCohomology A p) (y : groupCohomology B q) :
    (groupCohomology.map f (φ ⊗ₘ ψ : Rep.res f (A ⊗ B) ⟶ A' ⊗ B') (p + q)).hom (cup p q x y)
      = cup' p q ((groupCohomology.map f φ p).hom x) ((groupCohomology.map f ψ q).hom y) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_IsGradedCupProduct_map_cup.solution
