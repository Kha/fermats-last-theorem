import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.exists_root_fromNormalization_kummer_existsUnique_lift
    {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (hk : IsUnit ((k : ℕ) : R))
    (g : X.functionField) (hg : g ≠ 0)
    (r : ℕ) (U : Fin r → X.Opens) (hU : (⨆ a, U a) = ⊤) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (x : X), x ∈ U a →
      g / h a ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h a ^ k / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    let π := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization
    let Y := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).normalization
    ∃ (u : ∀ a, Γ(X, U a)) (T : ∀ a, Γ(Y, π ⁻¹ᵁ (U a))),

      (∀ a (x : X) (hx : x ∈ U a),
        algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ (U a) x hx (u a)) = g / h a ^ k) ∧
      (∀ a, IsUnit (u a)) ∧

      (∀ a, T a ^ k = π.app (U a) (u a)) ∧

      (∀ a b, ∃ w : Γ(X, U a ⊓ U b),
        (∀ (x : X) (hx : x ∈ U a ⊓ U b),
          algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ (U a ⊓ U b) x hx w) = h b / h a) ∧
        X.presheaf.map (homOfLE inf_le_left).op (u a) = w ^ k * X.presheaf.map (homOfLE inf_le_right).op (u b) ∧
        Y.presheaf.map (homOfLE (π.preimage_mono inf_le_left)).op (T a) =
          π.app (U a ⊓ U b) w * Y.presheaf.map (homOfLE (π.preimage_mono inf_le_right)).op (T b)) ∧

      (∀ a (Z : Scheme.{u}) (z : Z ⟶ X), z ⁻¹ᵁ (U a) = ⊤ →
        ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ k = z.app (U a) (u a) →
          ∃! s : Z ⟶ Y, s ≫ π = z ∧ s.app (π ⁻¹ᵁ (U a)) (T a) = Z.presheaf.map (homOfLE le_top).op τ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift.solution
