import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_smul_stdVertex_eq_of_mem_affinoid_zero
attribute [-simp] LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega~v_phi_eq_one_of_mem_affinoid_zero_of_v_det_lt_one"

theorem CerednikDrinfeld.Omega.smul_stdVertex_eq_of_mem_affinoid_zero
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K)
    {x : K} (g g' : GL (Fin 2) K₀)
    (hx  : pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ x ∈ affinoid ϖ₁ 0)
    (hx' : pmoebius K₀ (Matrix.ProjGenLinGroup.mk g')⁻¹ x ∈ affinoid ϖ₁ 0) :
    g • LT.LatticeTree.stdVertex R K₀ = g' • LT.LatticeTree.stdVertex R K₀ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_smul_stdVertex_eq_of_mem_affinoid_zero.solution
