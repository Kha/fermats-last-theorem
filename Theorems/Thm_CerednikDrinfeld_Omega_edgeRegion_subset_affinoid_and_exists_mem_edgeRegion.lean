import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_edgeRegion_subset_affinoid_and_exists_mem_edgeRegion

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.edgeRegion_subset_affinoid_and_exists_mem_edgeRegion
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ (c : K₀) (m : ℤ) (g : GL (Fin 2) K₀), (g : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1] →
      1 - (n : ℤ) ≤ m → m ≤ n → Valued.v (algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (-(n : ℤ)))) →
      vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
        vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ)) ⊆ affinoid ϖ n) ∧
    (∀ z : C, z ∈ affinoid ϖ n → ∃ (c : K₀) (m : ℤ) (g : GL (Fin 2) K₀),
      (g : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1] ∧ 1 - (n : ℤ) ≤ m ∧ m ≤ n ∧
      Valued.v (algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (-(n : ℤ)))) ∧
      z ∈ vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
        vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_edgeRegion_subset_affinoid_and_exists_mem_edgeRegion.solution
