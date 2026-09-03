import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_WalkOverlap
import Mathlib.Combinatorics.SimpleGraph.Paths
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_v_crossRatio_pmoebius_eq_zpow_walkOverlap
attribute [-simp] LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.v_crossRatio_pmoebius_eq_zpow_walkOverlap
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K) [DecidableEq (LT.LatticeTree.Vertex R K₀)]
    (g₁ g₂ g₃ g₄ : GL (Fin 2) K₀) {w₁ w₂ w₃ w₄ : K}
    (hw₁ : w₁ ∈ affinoid ϖ₁ 0) (hw₂ : w₂ ∈ affinoid ϖ₁ 0) (hw₃ : w₃ ∈ affinoid ϖ₁ 0) (hw₄ : w₄ ∈ affinoid ϖ₁ 0)
    (h13 : g₁ • LT.LatticeTree.stdVertex R K₀ ≠ g₃ • LT.LatticeTree.stdVertex R K₀)
    (h14 : g₁ • LT.LatticeTree.stdVertex R K₀ ≠ g₄ • LT.LatticeTree.stdVertex R K₀)
    (h23 : g₂ • LT.LatticeTree.stdVertex R K₀ ≠ g₃ • LT.LatticeTree.stdVertex R K₀)
    (h24 : g₂ • LT.LatticeTree.stdVertex R K₀ ≠ g₄ • LT.LatticeTree.stdVertex R K₀)
    (P : (CerednikDrinfeld.BruhatTits.tree R K₀).Path (g₁ • LT.LatticeTree.stdVertex R K₀) (g₂ • LT.LatticeTree.stdVertex R K₀))
    (Q : (CerednikDrinfeld.BruhatTits.tree R K₀).Path (g₃ • LT.LatticeTree.stdVertex R K₀) (g₄ • LT.LatticeTree.stdVertex R K₀)) :
    Valued.v (crossRatio (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₁) w₁) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₂) w₂)
        (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₃) w₃) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₄) w₄)) =
      Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
        (CerednikDrinfeld.Mumford.walkOverlap
          (P : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g₁ • LT.LatticeTree.stdVertex R K₀) (g₂ • LT.LatticeTree.stdVertex R K₀))
          (Q : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g₃ • LT.LatticeTree.stdVertex R K₀) (g₄ • LT.LatticeTree.stdVertex R K₀))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_v_crossRatio_pmoebius_eq_zpow_walkOverlap.solution
