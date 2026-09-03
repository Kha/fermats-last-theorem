import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (N : ℕ) (𝔓 : Scheme.Modules.ProjPresentation L f N) (h𝔓 : AlgebraicGeometry.IsClosedImmersion 𝔓.toProj)
    (i : Fin (N + 1)) (τ : 𝓡 1)
    (hτ : (λ_ L).hom.app ⊤ (ι 1 τ) = 𝔓.σ i) :
    θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) =
        𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i) ∧
      IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion.solution
