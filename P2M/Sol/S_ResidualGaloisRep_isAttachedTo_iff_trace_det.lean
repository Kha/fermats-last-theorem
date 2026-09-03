import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_LinearMap_charpoly_eq_iff_of_finrank_eq_two
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_isAttachedTo_iff_trace_det

theorem solution {k : Type} [Field k] (ρ : ResidualGaloisRep k) {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (φ : integralClosure ℤ ℂ →+* k) : ρ.IsAttachedTo f φ ↔ ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → (ℓ : k) ≠ 0 → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ → ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧ LinearMap.trace k ρ.V (ρ.ρ σ) = φ a ∧ LinearMap.det (ρ.ρ σ) = (ℓ : k) := by
  unfold ResidualGaloisRep.IsAttachedTo
  refine forall₄_congr fun ℓ _ _ _ ↦ forall₂_congr fun A _ ↦ forall₂_congr fun σ _ ↦ ?_
  refine exists_congr fun a ↦ and_congr_right fun _ ↦ ?_
  exact LinearMap.charpoly_eq_iff_of_finrank_eq_two ρ.finrank_eq (ρ.ρ σ) (φ a) ℓ
