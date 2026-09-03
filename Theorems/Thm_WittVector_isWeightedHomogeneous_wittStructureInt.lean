import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_isWeightedHomogeneous_wittStructureInt

universe v

theorem WittVector.isWeightedHomogeneous_wittStructureInt
    (p : ℕ) [Fact p.Prime] {idx : Type v} (Φ : MvPolynomial idx ℤ) (k : ℕ) (hΦ : Φ.IsHomogeneous k)
    (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun bi : idx × ℕ => p ^ bi.2) (wittStructureInt p Φ n)
      (k * p ^ n) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_isWeightedHomogeneous_wittStructureInt.solution
