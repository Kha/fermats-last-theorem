import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion

set_option autoImplicit false

open IsDedekindDomain NumberField

open scoped Classical in

theorem IsDedekindDomain.HeightOneSpectrum.exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (Ψ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ)
    (hcs : HasCompactSupport Ψ)
    (hlc : ∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.2 ≠ 1 → ∃ U ∈ nhds p, ∀ q ∈ U, Ψ q = Ψ p)
    (hcells : ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ * ‖(a : (v.adicCompletion K))‖ →
        ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ ≤ ρ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ →
          Ψ (a', t') = Ψ (a, t))
    (hgerm : ∃ C : ℝ, ∀ a t : (v.adicCompletion K)ˣ,
      ‖Ψ (a, t) - Ψ (a, 1)‖ ≤ C * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ *
        (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|)) :
    ∃ (Ψ₀ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ), IsLocallyConstant Ψ₀ ∧ HasCompactSupport Ψ₀ ∧
    ∃ (U₁ A : Subgroup (v.adicCompletion K)ˣ), IsOpen (U₁ : Set (v.adicCompletion K)ˣ) ∧ IsOpen (A : Set (v.adicCompletion K)ˣ) ∧ IsCompact (A : Set (v.adicCompletion K)ˣ) ∧
    ∃ (V : ℕ → Subgroup (v.adicCompletion K)ˣ), (∀ k, IsOpen (V k : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, V k ≤ U₁) ∧ (∀ k, V k ≤ A) ∧
    ∃ (sh : ℕ → Set (v.adicCompletion K)ˣ),
      (∀ k, sh k ⊆ (U₁ : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, IsCompact (sh k)) ∧ (∀ k, (1 : (v.adicCompletion K)ˣ) ∉ sh k) ∧
      (Pairwise fun k k' => Disjoint (sh k) (sh k')) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → t ≠ 1 → ∃ k, t ∈ sh k) ∧
      (∀ k, ∀ t ∈ sh k, ∀ τ ∈ V k, t * τ ∈ sh k) ∧
    ∃ (Fa : Finset (v.adicCompletion K)ˣ), (∀ α ∈ Fa, ∀ α' ∈ Fa, α ≠ α' → α⁻¹ * α' ∉ A) ∧
    ∃ (M₀ : ℕ) (C' : ℝ), 0 ≤ C' ∧
      (∀ a t : (v.adicCompletion K)ˣ, (∀ k, t ∉ sh k) → Ψ (a, t) = Ψ₀ (a, t)) ∧
      (∀ k, ∃ (Ft : Finset (v.adicCompletion K)ˣ) (c : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ → ℂ), Ft.card ≤ M₀ ∧
        (∀ τ ∈ Ft, ∀ τ' ∈ Ft, τ ≠ τ' → τ⁻¹ * τ' ∉ V k) ∧
        (∀ α τ, ‖c α τ‖ ≤ C' * ((k : ℝ) + 1) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ))) ∧
        ∀ a t : (v.adicCompletion K)ˣ, t ∈ sh k →
          Ψ (a, t) = Ψ₀ (a, t) +
            ∑ α ∈ Fa, ∑ τ ∈ Ft, c α τ * (if a⁻¹ * α ∈ A ∧ t⁻¹ * τ ∈ V k then 1 else 0)) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le.solution
