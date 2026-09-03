import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_finiteBySections_pullback_of_quasiFiniteAt

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_finiteBySections_pullback_of_quasiFiniteAt
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f] {M : X.Modules} {N : ℕ}
    (𝔔 : M.ProjPresentation f N) (𝔭 : PrimeSpectrum R)
    (hqf : ∀ x : X, f x = 𝔭 → 𝔔.toProj.QuasiFiniteAt x) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
        ∀ {X' : Scheme.{u}} (p : X' ⟶ X) (f' : X' ⟶ Spec (.of A)),
          IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap R A))) →
          Scheme.Modules.FiniteBySections ((Scheme.Modules.pullback p).obj M) f' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_finiteBySections_pullback_of_quasiFiniteAt.solution
