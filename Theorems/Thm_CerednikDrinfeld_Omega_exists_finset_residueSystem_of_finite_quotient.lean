import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_finset_residueSystem_of_finite_quotient

set_option autoImplicit false

theorem CerednikDrinfeld.Omega.exists_finset_residueSystem_of_finite_quotient
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    ∃ T : Finset K₀, (∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1) ∧
      (∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1) ∧
      (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t')) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_finset_residueSystem_of_finite_quotient.solution
