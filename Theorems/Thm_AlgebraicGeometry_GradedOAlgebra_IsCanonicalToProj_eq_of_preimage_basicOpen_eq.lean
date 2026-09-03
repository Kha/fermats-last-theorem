import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_eq_of_preimage_basicOpen_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.eq_of_preimage_basicOpen_eq
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤))
    (θ₁ θ₂ : X ⟶ Proj 𝓡)
    (h₁ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ₁)
    (h₂ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ₂)
    (hpre : ∀ (n : ℕ), 0 < n → ∀ σ : 𝓡 n,
      θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = θ₂ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
    (hpow : ∀ (n : ℕ), 0 < n → ∀ (σ : 𝓡 n) (k : ℕ),
      Scheme.Modules.IsFrameOn (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩) (θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))) :
    θ₁ = θ₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_eq_of_preimage_basicOpen_eq.solution
