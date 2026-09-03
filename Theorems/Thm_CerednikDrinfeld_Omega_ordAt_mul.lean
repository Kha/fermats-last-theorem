import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_ordAt_mul

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~isDomain_holRing~exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn~coordSub_dvd_of_apply_eq_zero"

theorem CerednikDrinfeld.Omega.ordAt_mul
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F G : ↥(holRing ϖ)) (hF : F ≠ 0) (hG : G ≠ 0) (z : ↥(upperHalfPlane K₀ K)) :
    ordAt ϖ (F * G) z = ordAt ϖ F z + ordAt ϖ G z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_ordAt_mul.solution
