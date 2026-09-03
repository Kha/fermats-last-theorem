import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_frobenius_comp_eq_comp_frobenius_of_forall_spec

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.frobenius_comp_eq_comp_frobenius_of_forall_spec
    (p : ℕ) [Fact p.Prime] {X Y : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of (ZMod p))) (fY : Y ⟶ Spec (CommRingCat.of (ZMod p)))
    (FX : X ⟶ X) (FY : Y ⟶ Y) (hFXb : FX ≫ fX = fX) (hFYb : FY ≫ fY = fY)
    (hFX : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ FX)
    (hFY : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (y : Spec (CommRingCat.of B) ⟶ Y),
        y ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ y = y ≫ FY)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) :
    FX ≫ g = g ≫ FY := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_frobenius_comp_eq_comp_frobenius_of_forall_spec.solution
