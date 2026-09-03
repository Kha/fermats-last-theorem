import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_RatPair_exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.RatPair.exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (Q : RatPair K) (t₀ π₀ : K) (hπ₀ : π₀ ≠ 0) :
    ∃ A B : RatPair K,
      A.IsPoleFreeOn ({z | Q.den.eval z ≠ 0} ∪ {z | Valued.v π₀ ≤ Valued.v (z - t₀)}) ∧
      A.num.degree < A.den.degree ∧
      B.IsPoleFreeOn ({z | Q.den.eval z ≠ 0} ∪ {z | Valued.v (z - t₀) < Valued.v π₀}) ∧
      ∀ z : K, Q.den.eval z ≠ 0 → Q.evalAt z = A.evalAt z + B.evalAt z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_RatPair_exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add.solution
