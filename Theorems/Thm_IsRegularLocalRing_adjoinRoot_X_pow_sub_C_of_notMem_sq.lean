import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_adjoinRoot_X_pow_sub_C_of_notMem_sq
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

open IsLocalRing Polynomial

theorem IsRegularLocalRing.adjoinRoot_X_pow_sub_C_of_notMem_sq
    {R : Type*} [CommRing R] [IsRegularLocalRing R] {t : R}
    (ht : t ∈ maximalIdeal R) (ht2 : t ∉ maximalIdeal R ^ 2) {n : ℕ} (hn : 0 < n) :
    IsRegularLocalRing (AdjoinRoot (X ^ n - C t : R[X])) ∧
    ringKrullDim (AdjoinRoot (X ^ n - C t : R[X])) = ringKrullDim R ∧
    (∀ N : Ideal (AdjoinRoot (X ^ n - C t : R[X])), N.IsMaximal →
      N = Ideal.span {AdjoinRoot.root (X ^ n - C t : R[X])} ⊔
        (maximalIdeal R).map (AdjoinRoot.of (X ^ n - C t : R[X]))) ∧
    IsSMulRegular (AdjoinRoot (X ^ n - C t : R[X])) (AdjoinRoot.root (X ^ n - C t : R[X])) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_adjoinRoot_X_pow_sub_C_of_notMem_sq.solution
