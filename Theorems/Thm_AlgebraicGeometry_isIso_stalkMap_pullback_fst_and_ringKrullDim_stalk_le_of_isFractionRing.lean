import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    (∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        IsIso ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap y)) ∧
    ∀ (n : ℕ),
      (∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
          ringKrullDim ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).presheaf.stalk y) ≤ n) →
      ∀ x : X, (f.base x).asIdeal = ⊥ → ringKrullDim (X.presheaf.stalk x) ≤ n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing.solution
