import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_RatPair_exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.RatPair.exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid
    {K₀ K : Type} [Field K₀] [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (n : ℕ) (r : RatPair K) (hr : r.IsPoleFreeOn (affinoid ϖ n)) :
    ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v (r.evalAt z) ≤ Valued.v b := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_RatPair_exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid.solution
