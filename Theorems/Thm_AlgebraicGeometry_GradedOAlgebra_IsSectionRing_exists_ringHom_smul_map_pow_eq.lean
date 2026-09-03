import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_ringHom_smul_map_pow_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_ringHom_smul_map_pow_eq
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (τ : 𝓡 1) (V : X.Opens) (hτ : AlgebraicGeometry.Scheme.Modules.IsFrameOn (ι 1 τ) V) :
    ∃ φ : R →+* Γ(X, V),
      (∀ a : S, φ (algebraMap S R a) =
        X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (AlgebraicGeometry.GradedOAlgebra.baseScalar f a)) ∧
      (∀ m : ℕ, AlgebraicGeometry.Scheme.Modules.IsFrameOn
        (ι (m • 1) ⟨(τ : R) ^ m, SetLike.pow_mem_graded m τ.2⟩) V) ∧
      (∀ (m : ℕ) (s : 𝓡 (m • 1)),
        φ (s : R) • (L.tensorPow (m • 1)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
            (ι (m • 1) ⟨(τ : R) ^ m, SetLike.pow_mem_graded m τ.2⟩) =
          (L.tensorPow (m • 1)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι (m • 1) s)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_ringHom_smul_map_pow_eq.solution
