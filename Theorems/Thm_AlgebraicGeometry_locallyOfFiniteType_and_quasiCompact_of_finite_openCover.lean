import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_locallyOfFiniteType_and_quasiCompact_of_finite_openCover

universe u
open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.locallyOfFiniteType_and_quasiCompact_of_finite_openCover
    {K : Type u} [CommRing K] {X J : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of K)} {σ : J ⟶ Spec (CommRingCat.of K)}
    [LocallyOfFiniteType f] [QuasiCompact f]
    {n : ℕ} (cov : Fin n → (X ⟶ J)) (hoi : ∀ i, IsOpenImmersion (cov i))
    (cov_over : ∀ i, cov i ≫ σ = f) (hcov : ⋃ i, Set.range (cov i).base = Set.univ) :
    LocallyOfFiniteType σ ∧ QuasiCompact σ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_locallyOfFiniteType_and_quasiCompact_of_finite_openCover.solution
