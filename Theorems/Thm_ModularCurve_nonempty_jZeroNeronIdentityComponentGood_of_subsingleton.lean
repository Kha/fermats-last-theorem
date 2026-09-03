import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponentGood
import P2M.Util
import P2M.Sol.S_ModularCurve_nonempty_jZeroNeronIdentityComponentGood_of_subsingleton

open ModularCurve

theorem ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_subsingleton (p : ℕ) [Fact p.Prime]
    (hC : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ p → ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
      Subsingleton (JZeroC (IsLocalRing.ResidueField ↥A') p))
    (h : Subsingleton (JZero p)) : Nonempty (JZeroNeronIdentityComponentGood p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_nonempty_jZeroNeronIdentityComponentGood_of_subsingleton.solution
