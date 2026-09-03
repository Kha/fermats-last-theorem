import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_finset_linearIndependent_residue_coeff

open AlgebraicCurve ModularCurve
theorem ModularCurve.exists_finset_linearIndependent_residue_coeff (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : LinearIndependent (AlgebraicClosure ℚ) s) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∀ hint : ∀ (i : Fin r) (k : ℤ), ((s i : LaurentSeries (AlgebraicClosure ℚ)).coeff k) ∈ A,
          LinearIndependent (IsLocalRing.ResidueField A)
            (fun i : Fin r => fun k : ℤ => IsLocalRing.residue A ⟨_, hint i k⟩) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_finset_linearIndependent_residue_coeff.solution
