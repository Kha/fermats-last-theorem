import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_finiteFlat_point_eq_one_of_pow_prime_pow_of_forall_dvr

theorem GaloisRep.finiteFlat_point_eq_one_of_pow_prime_pow_of_forall_dvr
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (hR : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O], Irreducible (ℓ : O) →
      ∀ (H' : Type) [CommRing H'] [HopfAlgebra O H'] [Module.Finite O H'] [Module.Flat O H'] [Coalgebra.IsCocomm O H']
        (x : WithConv (H' →ₐ[O] O)),
        (∀ h : H', x h - algebraMap O O (Coalgebra.counit h) ∈ IsLocalRing.maximalIdeal O) →
        ∀ k : ℕ, x ^ ℓ ^ k = 1 → x = 1)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H]
    [Module.Finite (GaloisRep.ratLocalizedAt ℓ) H] [Module.Flat (GaloisRep.ratLocalizedAt ℓ) H] [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) H]
    (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)) (hφ : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (φ h) = φ h)) (hφ1 : (∀ h : H, A.valuation (φ h - algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1)) (k : ℕ) (hφk : φ ^ ℓ ^ k = 1) :
    φ = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_finiteFlat_point_eq_one_of_pow_prime_pow_of_forall_dvr.solution
