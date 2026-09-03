import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_pseudoUniformizer_isExhausted_of_isCompact
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hK₀ : ∀ r : Γ₀, IsCompact {x : K | x ∈ Set.range (algebraMap K₀ K) ∧ Valued.v x ≤ r})
    (ϖ₀ : K₀) (h0 : 0 < Valued.v (algebraMap K₀ K ϖ₀)) (h1 : Valued.v (algebraMap K₀ K ϖ₀) < 1)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) :
    ∃ ϖ : PseudoUniformizer K₀ K, ϖ.ϖ = ϖ₀ ∧ IsExhausted ϖ ∧
      ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
        Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
          ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact.solution
