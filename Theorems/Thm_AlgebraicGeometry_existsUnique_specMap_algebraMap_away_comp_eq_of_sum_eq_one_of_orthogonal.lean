import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

universe u

theorem AlgebraicGeometry.existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal
    {S : Type u} [CommRing S] {m : ℕ} (ε : Fin m → S)
    (hε : ∀ k, IsIdempotentElem (ε k)) (hsum : ∑ k, ε k = 1) (horth : ∀ k l, k ≠ l → ε k * ε l = 0)
    {A : Scheme.{u}} (x : ∀ k, Spec (CommRingCat.of (Localization.Away (ε k))) ⟶ A) :
    ∃! y : Spec (CommRingCat.of S) ⟶ A,
      ∀ k, Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (ε k)))) ≫ y = x k := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal.solution
