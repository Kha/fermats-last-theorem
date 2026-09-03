import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import P2M.Util
import P2M.Sol.S_groupCohomology_d_cochainCup_apply

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory groupCohomology
theorem groupCohomology.d_cochainCup_apply {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) (p q : ℕ)
    (f : (Fin p → G) → A) (g : (Fin q → G) → B) (σ : Fin (p + q + 1) → G) :
    (inhomogeneousCochains.d (A ⊗ B) (p + q)).hom (groupCohomology.cochainCup A B p q f g) σ
      = groupCohomology.cochainCup A B (p + 1) q ((inhomogeneousCochains.d A p).hom f) g
          (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i))
        + ((-1 : k) ^ p) • groupCohomology.cochainCup A B p (q + 1) f ((inhomogeneousCochains.d B q).hom g) σ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_d_cochainCup_apply.solution
