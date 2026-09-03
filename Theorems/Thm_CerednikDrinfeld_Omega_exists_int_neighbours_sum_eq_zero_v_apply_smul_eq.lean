import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld CerednikDrinfeld.Omega~pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq~exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube~sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow~v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star CerednikDrinfeld.Mumford MulAction"

theorem CerednikDrinfeld.Omega.exists_int_neighbours_sum_eq_zero_v_apply_smul_eq
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hϖ₁ : ϖ₁.ϖ = algebraMap R K₀ ϖ)
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F) :
    ∃ m : LT.LatticeTree.Vertex R K₀ → ℤ,
      (∀ S : Finset (LT.LatticeTree.Vertex R K₀),
        (∀ y, y ∈ S ↔ (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y) → ∑ y ∈ S, m y = 0) ∧
      ∀ (y : LT.LatticeTree.Vertex R K₀), (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y →
        ∀ (g : GL (Fin 2) K₀), g • LT.LatticeTree.stdVertex R K₀ = y →
          ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
            Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
                ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
              Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
                Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (m y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq.solution
