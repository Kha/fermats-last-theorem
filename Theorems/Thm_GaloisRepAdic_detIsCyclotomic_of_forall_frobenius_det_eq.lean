import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_detIsCyclotomic_of_forall_frobenius_det_eq
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

theorem GaloisRepAdic.detIsCyclotomic_of_forall_frobenius_det_eq
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) (S : Finset ℕ)
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        LinearMap.det (ρ.ρ τ) = (ℓ : A)) :
    ρ.DetIsCyclotomic p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_detIsCyclotomic_of_forall_frobenius_det_eq.solution
