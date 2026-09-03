import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped Classical in

theorem AutomorphicForm.continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (thr : HeightOneSpectrum (𝓞 F) → ℤ)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (_hthr : ∀ v ∉ S, thr v = 0)
    (_hΦd : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F), Differentiable ℂ (Φ j v w))
    (_hΦ1 : ∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (_hΦ0 : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F) (s : ℂ), w ≠ 0 →
      WithZero.exp (thr v) < Valued.v w → Φ j v w s = 0)
    (_hΦb : ∀ R : ℝ, ∃ (M : ℝ) (κ : ℕ), 0 ≤ M ∧ ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F))
      (w : v.adicCompletion F) (e : ℤ) (s : ℂ), ‖s‖ ≤ R → Valued.v w = WithZero.exp e →
        ‖Φ j v w s‖ ≤ (if v ∈ S then M else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ)
    (_hΦlc : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w₀ : v.adicCompletion F), w₀ ≠ 0 → ∃ δ : ℤ,
      ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v (w - w₀) ≤ WithZero.exp δ → Φ j v w s = Φ j v w₀ s) :
    (∀ (x₀ : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n),
      Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        Φ j v (((x₀ : AdeleRing (𝓞 F) F) * (p.2 : AdeleRing (𝓞 F) F)).2 v) p.1) ∧
    (∀ (U : Set (AdeleRing (𝓞 F) F)ˣ), IsCompact U → ∀ R : ℝ,
      ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (c₀ c : ℝ), 0 < c₀ ∧ 0 ≤ c ∧
        (∀ ξ : F, ξ ∈ I → ξ ≠ 0 → c₀ ≤ ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ∧
        ∀ (j : Fin n) (s : ℂ), ‖s‖ ≤ R → ∀ u ∈ U, ∀ ξ : F, ξ ≠ 0 →
          (ξ ∉ I → ∏ᶠ v : HeightOneSpectrum (𝓞 F),
              Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (u : AdeleRing (𝓞 F) F)).2 v) s = 0) ∧
          ‖∏ᶠ v : HeightOneSpectrum (𝓞 F),
              Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (u : AdeleRing (𝓞 F) F)).2 v) s‖
            ≤ c * (max 1 ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ^ k) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact.solution
