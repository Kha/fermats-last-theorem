import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int

    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [Smooth f]

    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (x : Spec (CommRingCat.of k) ⟶ X),
      ∃ v : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
        v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ x ≫ f ∧
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ v = x ∧
        ∀ t : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
          t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ x ≫ f →
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ t = x →
          ∃! c : k, t = Spec.map (CommRingCat.ofHom
            (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom) ≫ v) :
    SmoothOfRelativeDimension 1 f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.solution
