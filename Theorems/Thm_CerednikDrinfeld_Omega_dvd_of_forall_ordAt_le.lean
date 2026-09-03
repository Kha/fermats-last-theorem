import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_dvd_of_forall_ordAt_le

set_option autoImplicit false

open CerednikDrinfeld.Omega hiding exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero ordAt_mul finite_setOf_apply_eq_zero_of_mem_holOn_affinoid

theorem CerednikDrinfeld.Omega.dvd_of_forall_ordAt_le
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F G : ↥(holRing ϖ)) (hG : G ≠ 0)
    (h : ∀ z : ↥(upperHalfPlane K₀ K), ordAt ϖ G z ≤ ordAt ϖ F z) :
    G ∣ F := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_dvd_of_forall_ordAt_le.solution
