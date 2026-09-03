import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_natCard_algHom_int_eq_natCard_algHom_fixed_of_finite_of_liesOverPrime

theorem ValuationSubring.natCard_algHom_int_eq_natCard_algHom_fixed_of_finite_of_liesOverPrime
    (p : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (K : Type) [CommRing K] [Algebra ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ)
        (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K)) :
    Nat.card (K →ₐ[ℤ] ℤ)
      = Nat.card {φ : K →ₐ[ℤ] ↥A //
          ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (x : K),
            σ (φ x : AlgebraicClosure ℚ) = (φ x : AlgebraicClosure ℚ)} := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_natCard_algHom_int_eq_natCard_algHom_fixed_of_finite_of_liesOverPrime.solution
