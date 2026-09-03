import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (c : K₀) (m : ℤ) (g : GL (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1]) :
    vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) =
        {z : C | Valued.v (z - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ≤ Valued.v (z - algebraMap K₀ C a)} ∧
      edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) =
        {z : C | Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) < Valued.v (z - algebraMap K₀ C c) ∧
          Valued.v (z - algebraMap K₀ C c) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1)))} ∧
      vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ)) =
        {z : C | Valued.v (z - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) ≤ Valued.v (z - algebraMap K₀ C a)} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine.solution
