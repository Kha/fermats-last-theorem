import Mathlib
import Definitions.Def_ModularCurve_MazurPrincipleCore
import P2M.Util
import P2M.Sol.S_ModularCurve_not_isEventuallyEisenstein_of_repClauses
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

theorem ModularCurve.not_isEventuallyEisenstein_of_repClauses
    (𝔪 : Ideal ModularCurve.HeckeAlg) (hmax : 𝔪.IsMaximal)
    (ρmat : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (ModularCurve.HeckeAlg ⧸ 𝔪))
    (hirr : ∀ Wsub : Submodule (ModularCurve.HeckeAlg ⧸ 𝔪) (Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪),
      (∀ g, ∀ v ∈ Wsub, (ρmat g).mulVec v ∈ Wsub) → Wsub = ⊥ ∨ Wsub = ⊤)
    (Sρ : Finset ℕ)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ Sρ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          (ρmat σ).trace = Ideal.Quotient.mk 𝔪 (ModularCurve.heckeGen ⟨ℓ, hℓ⟩))
    (hdet : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ Sρ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          (ρmat σ).det = ((ℓ : ℕ) : ModularCurve.HeckeAlg ⧸ 𝔪))
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρmat.ker) :
    ¬ ModularCurve.IsEventuallyEisenstein 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_not_isEventuallyEisenstein_of_repClauses.solution
