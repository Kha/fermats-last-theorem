import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_blaschke_denominators

set_option autoImplicit false

open Filter CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_blaschke_denominators
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {ι : Type} (w : ι → K) (hw : ∀ γ, w γ ∈ upperHalfPlane K₀ K)
    (hfin : ∀ n : ℕ, {γ : ι | w γ ∈ affinoid ϖ n}.Finite) :
    ∃ d : ι → Polynomial K,
      (∀ γ, (d γ).natDegree ≤ 1) ∧
      (∀ γ, ∀ z ∈ upperHalfPlane K₀ K, (d γ).eval z ≠ 0) ∧
      (∀ (n : ℕ) (γ : ι) (w' : K), ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v ((z - w') / (d γ).eval z) ≤ Valued.v b) ∧
      (∀ (n : ℕ) (c : K), c ≠ 0 →
        ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n, Valued.v ((z - w γ) / (d γ).eval z - 1) < Valued.v c) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_blaschke_denominators.solution
