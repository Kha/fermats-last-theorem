import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_RatPair_v_evalAt_lt_of_forall_v_evalAt_add_evalAt_lt_on_sphere

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.RatPair.v_evalAt_lt_of_forall_v_evalAt_add_evalAt_lt_on_sphere
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (A B : RatPair K) (t₀ π₀ : K) (hπ₀ : π₀ ≠ 0) (Z : Finset K)
    (hA : A.IsPoleFreeOn {z | Valued.v π₀ ≤ Valued.v (z - t₀)})
    (hA0 : A.num.degree < A.den.degree)
    (hB : B.IsPoleFreeOn {z | Valued.v (z - t₀) < Valued.v π₀})
    (hBC : ∀ z : K, Valued.v (z - t₀) = Valued.v π₀ → (∀ ζ ∈ Z, Valued.v π₀ ≤ Valued.v (z - ζ)) → B.den.eval z ≠ 0)
    (b : K)
    (hb : ∀ z : K, Valued.v (z - t₀) = Valued.v π₀ → (∀ ζ ∈ Z, Valued.v π₀ ≤ Valued.v (z - ζ)) →
      Valued.v (A.evalAt z + B.evalAt z) < Valued.v b) :
    (∀ z : K, Valued.v π₀ ≤ Valued.v (z - t₀) → Valued.v (A.evalAt z) < Valued.v b) ∧
    (∀ z : K, Valued.v (z - t₀) < Valued.v π₀ → Valued.v (B.evalAt z) < Valued.v b) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_RatPair_v_evalAt_lt_of_forall_v_evalAt_add_evalAt_lt_on_sphere.solution
