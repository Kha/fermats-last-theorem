import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.coordSub_dvd_of_apply_eq_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K))
    (hF : (F : ↥(upperHalfPlane K₀ K) → K) z = 0) :
    coordSub ϖ z ∣ F := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero.solution
