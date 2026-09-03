import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_chain_affine_edgeRegion_cover_affinoid

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega~edgeRegion_subset_affinoid_and_exists_mem_edgeRegion~vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine~exists_fin_ballEdges~chain_clauses_of_ballEdges"

theorem CerednikDrinfeld.Omega.exists_chain_affine_edgeRegion_cover_affinoid
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (k : ℕ) (P : Fin (k + 1) → Set C) (g : Fin (k + 1) → GL (Fin 2) K₀)
      (t π : Fin (k + 1) → C) (Z : Fin (k + 1) → Finset C),

      (∀ j, P j = (vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g j)) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk (g j)) ∪
            vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g j * edgeFlip K₀ ϖ)))) ∧

      (∀ j, ∃ (c : K₀) (m : ℤ), ((g j : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1]) ∧

      (∀ j, P j ⊆ affinoid ϖ n) ∧ (affinoid ϖ n ⊆ ⋃ j, P j) ∧

      (∀ j, j ≠ 0 → π j ≠ 0) ∧
      (∀ j, j ≠ 0 → ∀ i, i < j → ∀ z ∈ P i, Valued.v (π j) ≤ Valued.v (z - t j)) ∧
      (∀ j, j ≠ 0 → ∀ z ∈ P j, (∃ i, i < j ∧ z ∈ P i) ∨ Valued.v (z - t j) < Valued.v (π j)) ∧
      (∀ j, j ≠ 0 → ∀ z : C, Valued.v (z - t j) = Valued.v (π j) →
        (∀ ζ ∈ Z j, Valued.v (π j) ≤ Valued.v (z - ζ)) → z ∈ P j ∧ ∃ i, i < j ∧ z ∈ P i) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_chain_affine_edgeRegion_cover_affinoid.solution
