import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_v_apply_le
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_isUnit_of_v_apply_eq

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (f : ↥(holRing ϖ)) (hf : IsUnit f)
    (hv : ∀ z w : ↥(upperHalfPlane K₀ K),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) w)) :
    ∃ c : K, f = algebraMap K ↥(holRing ϖ) c := by
  rcases isEmpty_or_nonempty ↥(upperHalfPlane K₀ K) with hE | hne
  · exact CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_v_apply_le K₀ K ϖ hrk hex hfin f 0
      (fun z => (hE.false z).elim)
  · obtain ⟨z₀⟩ := hne
    exact CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_v_apply_le K₀ K ϖ hrk hex hfin f
      ((f : ↥(upperHalfPlane K₀ K) → K) z₀) (fun z => (hv z z₀).le)
