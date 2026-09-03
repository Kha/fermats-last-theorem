import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_adj_min_le_v_apply_le_max_of_isUnit

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_adj_min_le_v_apply_le_max_of_isUnit
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (ϖ₁ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ₁)
    (f : ↥(holRing ϖ₁)) (hf : IsUnit f) (z : ↥(upperHalfPlane K₀ K)) :
    ∃ (g g' : GL (Fin 2) K₀) (w w' : K) (y y' : ↥(upperHalfPlane K₀ K)),
      w ∈ affinoid ϖ₁ 0 ∧ w' ∈ affinoid ϖ₁ 0 ∧
      (y : K) = pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w ∧
      (y' : K) = pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w' ∧
      (CerednikDrinfeld.BruhatTits.tree R K₀).Adj (g • LT.LatticeTree.stdVertex R K₀)
        (g' • LT.LatticeTree.stdVertex R K₀) ∧
      min (Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) y)) (Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) y')) ≤
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ∧
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ≤
        max (Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) y)) (Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) y')) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_adj_min_le_v_apply_le_max_of_isUnit.solution
