import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.AffineLimit.locallyOfFiniteType_of_forall_exists_fg_factor {R : Type u} [CommRing R] {X : Scheme.{u}}
    (ξ : X ⟶ Spec (CommRingCat.of R))
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X),
      φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
      ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of ↥A₀) ⟶ X),
        φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀)) ∧
        Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ) :
    LocallyOfFiniteType ξ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor.solution
