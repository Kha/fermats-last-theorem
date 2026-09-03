import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isFinite_to_proj_of_completeOrthogonalIdempotents

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isFinite_to_proj_of_completeOrthogonalIdempotents
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {m : ℕ} (e : Fin m → R)
    (he : CompleteOrthogonalIdempotents e)
    (hfin : ∀ i : Fin m, ∃ (A σ : Type u) (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ)
      (_ : GradedRing 𝒜)
      (ι : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e i))))) ⟶ Proj 𝒜),
      IsFinite ι) :
    ∃ (A σ : Type u) (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ)
      (_ : GradedRing 𝒜) (ι : X ⟶ Proj 𝒜), IsFinite ι := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isFinite_to_proj_of_completeOrthogonalIdempotents.solution
