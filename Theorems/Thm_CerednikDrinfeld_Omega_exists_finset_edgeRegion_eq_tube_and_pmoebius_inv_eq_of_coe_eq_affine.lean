import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega~vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine~exists_finset_residueSystem_of_finite_quotient"

theorem CerednikDrinfeld.Omega.exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (c : K₀) (m : ℤ) (g : GL (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1]) :
    (∃ (H : Finset C) (ρ : C → C), (∀ h ∈ H, ρ h ≠ 0) ∧
      ∀ z : C, z ∈ (vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
          vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) ↔
        Valued.v (z - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ∧
          ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h)) ∧
    (∀ z : C, pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z =
      (z - algebraMap K₀ C c) / algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine.solution
