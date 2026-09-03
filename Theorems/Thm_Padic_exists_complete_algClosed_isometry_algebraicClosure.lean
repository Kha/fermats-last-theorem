import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_Padic_exists_complete_algClosed_isometry_algebraicClosure

open scoped NNReal
theorem Padic.exists_complete_algClosed_isometry_algebraicClosure
    (p : ℕ) [Fact p.Prime] :
    ∃ (K : Type) (_ : NontriviallyNormedField K) (_ : IsUltrametricDist K)
      (_ : CompleteSpace K) (_ : CharZero K) (_ : IsAlgClosed K) (_ : Algebra ℚ_[p] K),
      (∀ x : ℚ_[p], ‖algebraMap ℚ_[p] K x‖ = ‖x‖) ∧
      ∃ (ι : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] K),
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]),
          ∃ (σK : K →+* K), Isometry ⇑σK ∧ (∀ x, σK (ι x) = ι (σ x)) := by p2m_exact_reverting @_root_.P2MW.S_Padic_exists_complete_algClosed_isometry_algebraicClosure.solution
