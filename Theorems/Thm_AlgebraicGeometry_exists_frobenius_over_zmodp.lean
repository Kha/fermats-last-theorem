import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_frobenius_over_zmodp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_frobenius_over_zmodp
    (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (ZMod p))) :
    ∃ F : X ⟶ X, F ≫ f = f ∧
      ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_frobenius_over_zmodp.solution
