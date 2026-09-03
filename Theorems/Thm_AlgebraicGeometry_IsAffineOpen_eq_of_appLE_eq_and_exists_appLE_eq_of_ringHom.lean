import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsAffineOpen_eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.IsAffineOpen.eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (W : X.Opens) (hW : IsAffineOpen W) :
    (∀ (p q : Spec (CommRingCat.of K) ⟶ X), p ≫ f = 𝟙 _ → q ≫ f = 𝟙 _ →
      ∀ (hp : ⊤ ≤ p ⁻¹ᵁ W) (hq : ⊤ ≤ q ⁻¹ᵁ W),
        p.appLE W ⊤ hp ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
          q.appLE W ⊤ hq ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom → p = q) ∧
    (∀ ν : Γ(X, W) →+* K,
        ν.comp ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ W le_top).hom = RingHom.id K →
        ∃ (p : Spec (CommRingCat.of K) ⟶ X) (_ : p ≫ f = 𝟙 _) (hp : ⊤ ≤ p ⁻¹ᵁ W),
          (p.appLE W ⊤ hp ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom = ν) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsAffineOpen_eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom.solution
