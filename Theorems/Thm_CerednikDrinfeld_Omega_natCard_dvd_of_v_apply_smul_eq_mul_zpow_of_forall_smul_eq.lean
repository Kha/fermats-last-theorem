import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.OrderOfElement
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld CerednikDrinfeld.Omega~exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube CerednikDrinfeld.Mumford MulAction"

theorem CerednikDrinfeld.Omega.natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hϖ₁ : ϖ₁.ϖ = algebraMap R K₀ ϖ)
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F)
    (y : LT.LatticeTree.Vertex R K₀) (hy : (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y)
    (H : Subgroup PGL(2, K₀)) [Finite ↥H]
    (hH0 : ∀ h ∈ H, h • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀)
    (hHy : ∀ h ∈ H, h • y = y)
    (htame : Valued.v ((Nat.card ↥H : ℕ) : K) = 1)
    (hinv : ∀ h ∈ H, ∀ z : ↥(upperHalfPlane K₀ K),
      (F : ↥(upperHalfPlane K₀ K) → K) (h • z) = (F : ↥(upperHalfPlane K₀ K) → K) z)
    (m : ℤ)
    (hm : ∀ (g : GL (Fin 2) K₀), g • LT.LatticeTree.stdVertex R K₀ = y →
      ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
            ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
          Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
            Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ m) :
    ((Nat.card ↥H : ℕ) : ℤ) ∣ m := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq.solution
