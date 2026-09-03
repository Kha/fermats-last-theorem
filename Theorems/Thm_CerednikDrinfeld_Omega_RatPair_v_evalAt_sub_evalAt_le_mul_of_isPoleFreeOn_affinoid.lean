import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_RatPair_v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~gaussNorm_add_eq_max_of_separated_poles"

theorem CerednikDrinfeld.Omega.RatPair.v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (n m : ℕ) (hnm : n ≤ m)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ m)
    (r : RatPair K) (hr : r.IsPoleFreeOn (affinoid ϖ m))
    (b : K) (hb : ∀ w : K, w ∈ affinoid ϖ m → Valued.v (r.evalAt w) ≤ Valued.v b)
    {z z₀ : K} (hz : z ∈ affinoid ϖ n) (hz₀ : z₀ ∈ affinoid ϖ n) :
    Valued.v (r.evalAt z - r.evalAt z₀) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - n) * Valued.v b := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_RatPair_v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid.solution
