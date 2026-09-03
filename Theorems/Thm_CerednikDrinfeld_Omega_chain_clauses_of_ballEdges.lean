import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_chain_clauses_of_ballEdges

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.chain_clauses_of_ballEdges
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (n : ℕ) (k : ℕ) (cen : Fin (k + 1) → K₀) (lev : Fin (k + 1) → ℤ)
    (hlev0 : lev 0 = 1 - (n : ℤ))
    (hroot : ∀ j, Valued.v (algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (-(n : ℤ)))))
    (hlow : ∀ j, 1 - (n : ℤ) ≤ lev j)
    (hmono : ∀ i j, i ≤ j → lev i ≤ lev j)
    (hdist : ∀ i j, i ≠ j → lev i = lev j →
      Valued.v (algebraMap K₀ C (ϖ.ϖ ^ lev j)) < Valued.v (algebraMap K₀ C (cen i) - algebraMap K₀ C (cen j)))
    (hpar : ∀ j, lev j = 1 - (n : ℤ) ∨ ∃ i, i < j ∧ lev i = lev j - 1 ∧
      Valued.v (algebraMap K₀ C (cen j) - algebraMap K₀ C (cen i)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))))
    (P : Fin (k + 1) → Set C)
    (hP : ∀ j, P j = ({z : C | Valued.v (z - algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - algebraMap K₀ C a)} ∪
        {z : C | Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) < Valued.v (z - algebraMap K₀ C (cen j)) ∧
          Valued.v (z - algebraMap K₀ C (cen j)) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)))} ∪
        {z : C | Valued.v (z - algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) ≤ Valued.v (z - algebraMap K₀ C a)})) :
    (∀ j, j ≠ 0 → algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)) ≠ 0) ∧
    (∀ j, j ≠ 0 → ∀ i, i < j → ∀ z ∈ P i,
      Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - algebraMap K₀ C (cen j))) ∧
    (∀ j, j ≠ 0 → ∀ z ∈ P j, (∃ i, i < j ∧ z ∈ P i) ∨
      Valued.v (z - algebraMap K₀ C (cen j)) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)))) ∧
    ∃ Z : Fin (k + 1) → Finset C,
      ∀ j, j ≠ 0 → ∀ z : C, Valued.v (z - algebraMap K₀ C (cen j)) = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) →
        (∀ ζ ∈ Z j, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - ζ)) → z ∈ P j ∧ ∃ i, i < j ∧ z ∈ P i := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_chain_clauses_of_ballEdges.solution
