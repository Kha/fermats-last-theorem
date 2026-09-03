import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_fin_ballEdges

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_fin_ballEdges
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) [Finite (R ⧸ Ideal.span {ϖ₀})]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (k : ℕ) (cen : Fin (k + 1) → K₀) (lev : Fin (k + 1) → ℤ),
      cen 0 = 0 ∧ lev 0 = 1 - (n : ℤ) ∧
      (∀ i j, i ≤ j → lev i ≤ lev j) ∧
      (∀ i j, i ≠ j → lev i = lev j → ¬ IsLocalization.IsInteger R ((cen i - cen j) / algebraMap R K₀ ϖ₀ ^ lev j)) ∧
      (∀ j, lev j = 1 - (n : ℤ) ∨
        ∃ i, i < j ∧ lev i = lev j - 1 ∧ IsLocalization.IsInteger R ((cen j - cen i) / algebraMap R K₀ ϖ₀ ^ (lev j - 1))) ∧
      (∀ j, (1 - (n : ℤ) ≤ lev j ∧ lev j ≤ (n : ℤ) ∧ IsLocalization.IsInteger R (cen j * algebraMap R K₀ ϖ₀ ^ n))) ∧
      (∀ (c : K₀) (m : ℤ), (1 - (n : ℤ) ≤ m ∧ m ≤ (n : ℤ) ∧ IsLocalization.IsInteger R (c * algebraMap R K₀ ϖ₀ ^ n)) →
        ∃ j, lev j = m ∧ IsLocalization.IsInteger R ((c - cen j) / algebraMap R K₀ ϖ₀ ^ m)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_fin_ballEdges.solution
