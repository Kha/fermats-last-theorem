import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ModularCurve_det_eq_natCast_of_forall_rootsOfUnity_of_det_frobenius_eq_natCast
attribute [-instance] AlgebraicClosure.Rat.isGalois FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
set_option autoImplicit false
open ModularCurve

theorem ModularCurve.det_eq_natCast_of_forall_rootsOfUnity_of_det_frobenius_eq_natCast
    (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (S : Finset ℕ)
    (hdet : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → (ρ σ).det = (a : HeckeAlg ⧸ 𝔪) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_det_eq_natCast_of_forall_rootsOfUnity_of_det_frobenius_eq_natCast.solution
