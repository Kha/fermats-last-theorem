import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_base_apply_eq_and_surjective_and_locallyQuasiFinite_and_isFinite_of_frobenius_pin

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.base_apply_eq_and_surjective_and_locallyQuasiFinite_and_isFinite_of_frobenius_pin
    (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (ZMod p))) [LocallyOfFiniteType f]
    (F : X ⟶ X) (hFb : F ≫ f = f)
    (hF : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ F) :
    (∀ x : X, F.base x = x) ∧ Surjective F ∧ QuasiCompact F ∧ LocallyQuasiFinite F ∧ IsAffineHom F ∧ IsFinite F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_base_apply_eq_and_surjective_and_locallyQuasiFinite_and_isFinite_of_frobenius_pin.solution
