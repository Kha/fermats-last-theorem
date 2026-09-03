import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing
    {S : Type u} [CommRing S] [IsLocalRing S] (I : Ideal S) [IsAdicComplete I S] {X : Scheme.{u}}
    (x : ∀ n : ℕ, Spec (CommRingCat.of (S ⧸ I ^ (n + 1))) ⟶ X)
    (hx : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))) ≫ x (n + 1) = x n) :
    ∃! y : Spec (CommRingCat.of S) ⟶ X,
      ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ y = x n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing.solution
