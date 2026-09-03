import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_inhomogeneousCochains_d_comp_res_apply

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.inhomogeneousCochains_d_comp_res_apply
    {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep.{0} k G} {B : Rep.{0} k H}
    (f : H →* G) (T : A →+ B) (hT : ∀ (h : H) (a : A), T (A.ρ (f h) a) = B.ρ h (T a)) (n : ℕ)
    (x : (Fin n → G) → A) :
    ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => T (x (f ∘ g))) =
      fun g => T (((inhomogeneousCochains A).d n (n + 1)).hom x (f ∘ g)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_inhomogeneousCochains_d_comp_res_apply.solution
