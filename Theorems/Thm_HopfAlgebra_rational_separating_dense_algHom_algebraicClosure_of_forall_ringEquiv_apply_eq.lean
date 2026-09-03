import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_rational_separating_dense_algHom_algebraicClosure_of_forall_ringEquiv_apply_eq

theorem HopfAlgebra.rational_separating_dense_algHom_algebraicClosure_of_forall_ringEquiv_apply_eq
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Module.Flat ℤ K]
    (ℓ : ℕ) (hfin : Module.Finite (GaloisRep.ratLocalizedAt ℓ)
      (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    [Finite (K →ₐ[ℤ] AlgebraicClosure ℚ)]
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k) :
    (∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K), ∃ r : ℚ, ψ k = algebraMap ℚ _ r) ∧
    (∀ k k' : K, (∀ ψ : K →ₐ[ℤ] AlgebraicClosure ℚ, ψ k = ψ k') → k = k') ∧
    (∀ c : (K →ₐ[ℤ] AlgebraicClosure ℚ) → ℤ, ∃ (k : K) (N : ℕ), 0 < N ∧
      ∀ ψ : K →ₐ[ℤ] AlgebraicClosure ℚ, ψ k = ((N : ℤ) * c ψ : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_rational_separating_dense_algHom_algebraicClosure_of_forall_ringEquiv_apply_eq.solution
