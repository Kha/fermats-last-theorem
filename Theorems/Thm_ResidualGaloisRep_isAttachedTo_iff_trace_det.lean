import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isAttachedTo_iff_trace_det

open Polynomial

theorem ResidualGaloisRep.isAttachedTo_iff_trace_det {k : Type} [Field k] (ρ : ResidualGaloisRep k) {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (φ : integralClosure ℤ ℂ →+* k) : ρ.IsAttachedTo f φ ↔ ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → (ℓ : k) ≠ 0 → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ → ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧ LinearMap.trace k ρ.V (ρ.ρ σ) = φ a ∧ LinearMap.det (ρ.ρ σ) = (ℓ : k) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isAttachedTo_iff_trace_det.solution
