import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_two_cocycle_coind_apply_one_eq

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.exists_two_cocycle_coind_apply_one_eq
    {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (A : Rep k S)
    (c : (Fin 2 → S) → A) (hc : inhomogeneousCochains.d A 2 c = 0) :
    ∃ (F : (Fin 2 → G) → Rep.coind S.subtype A)
      (_ : inhomogeneousCochains.d (Rep.coind S.subtype A) 2 F = 0),
      ∀ s : Fin 2 → S, (F (fun i => (s i : G))).1 1 = c s := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_two_cocycle_coind_apply_one_eq.solution
