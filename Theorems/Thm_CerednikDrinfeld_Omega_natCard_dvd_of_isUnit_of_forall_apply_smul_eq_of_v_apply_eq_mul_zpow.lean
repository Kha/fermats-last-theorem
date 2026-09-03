import Definitions.Def_CerednikDrinfeld_OmegaTubes
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_natCard_dvd_of_isUnit_of_forall_apply_smul_eq_of_v_apply_eq_mul_zpow

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.natCard_dvd_of_isUnit_of_forall_apply_smul_eq_of_v_apply_eq_mul_zpow
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (H : Subgroup PGL(2, K₀)) [Finite H]
    (hH : ∀ h ∈ H, ∀ z : K, z ∈ stdEdgeTube ϖ → pmoebius K₀ h z ∈ stdEdgeTube ϖ)
    (hdir : ∀ h ∈ H, ∀ z : K, z ∈ stdEdgeTube ϖ → Valued.v (pmoebius K₀ h z) = Valued.v z)
    (htame : Valued.v ((Nat.card H : ℕ) : K) = 1)
    (f : ↥(holRing ϖ)) (hf : IsUnit f)
    (hinv : ∀ h ∈ H, ∀ z : ↥(upperHalfPlane K₀ K), (z : K) ∈ stdEdgeTube ϖ →
      (f : ↥(upperHalfPlane K₀ K) → K) (h • z) = (f : ↥(upperHalfPlane K₀ K) → K) z)
    (c : Γ₀) (m : ℤ)
    (hcm : ∀ (z : K) (hz : z ∈ stdEdgeTube ϖ),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩) = c * Valued.v z ^ m) :
    ((Nat.card H : ℕ) : ℤ) ∣ m := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_natCard_dvd_of_isUnit_of_forall_apply_smul_eq_of_v_apply_eq_mul_zpow.solution
