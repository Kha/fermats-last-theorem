import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (X : Set (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (hXc : IsCompact X) (hX0 : X.Nonempty)
    (ιE : Type) [Countable ιE] (nE : ιE → ℕ)
    (A B : ιE → HeightOneSpectrum (𝓞 K) → ℂ) (hA : ∀ e v, A e v ≠ 0) (hB : ∀ e v, B e v ≠ 0)
    (M₀ : HeightOneSpectrum (𝓞 K) → ℝ) (hAM : ∀ e v, ‖A e v‖ ≤ M₀ v) (hBM : ∀ e v, ‖B e v‖ ≤ M₀ v)
    (τ : ιE → ℝ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ))
    (hτ : ∀ (e : ιE) (t : ℝ) (v : HeightOneSpectrum (𝓞 K)), v ∉ SK →
      τ e t v = ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
          (A e v * (HeckeEigensystem.cNorm v) ^ (-((t : ℂ) * Complex.I)) + B e v * (HeckeEigensystem.cNorm v) ^ ((t : ℂ) * Complex.I)),
        (HeckeEigensystem.cNorm v) * A e v * B e v))
    (hτS : ∀ (e : ιE) (t : ℝ) (v : HeightOneSpectrum (𝓞 K)), v ∈ SK → τ e t v = 0)
    (hτX : ∀ e t, τ e t ∈ X)
    (κ c : ℂ)
    (P Q U V a : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ)
    (hPc : ∀ e i j t, P e i j t = P e i j 0)
    (hQc : ∀ e i j, Continuous (Q e i j)) (hUc : ∀ e i j, Continuous (U e i j)) (hVc : ∀ e i j, Continuous (V e i j))
    (hac : ∀ e i j, Continuous (a e i j)) (hai : ∀ e i j, Integrable (a e i j))
    (haQ : ∀ e i j, Integrable (fun t => a e i j t * Q e i j t))
    (haU : ∀ e i j, Integrable (fun t => a e i j t * U e i j t))
    (haV : ∀ e i j, Integrable (fun t => a e i j t * V e i j t))
    (hUV0 : ∀ e i j, U e i j 0 = V e i j 0)
    (L : ιE → ℝ) (hL : Summable L)
    (hL1 : ∀ e, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
        ∫ t : ℝ, (‖a e i j t‖ * (1 + ‖P e i j t‖) + ‖a e i j t * Q e i j t‖ +
          ‖a e i j t * U e i j t‖ + ‖a e i j t * V e i j t‖) ≤ L e)
    (hL0 : ∀ e, ∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j 0‖ * (‖U e i j 0‖ + ‖V e i j 0‖) ≤ L e)
    (hLip : ∀ (e : ιE) (t : ℝ), |t| ≤ 1 →
        (∑ i : Fin (nE e), ∑ j : Fin (nE e),
          ‖a e i j t * (U e i j t + V e i j t) - a e i j 0 * (U e i j 0 + V e i j 0)‖) ≤ L e * |t| ∧
        (∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j t * (U e i j t - V e i j t)‖) ≤ L e * |t|) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 → ∃ e : ιE, 0 < nE e ∧ tabs n = τ e 0) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
      ∃ s : C(X, ℂ) →L[ℂ] ℂ,
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ),
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).1 ^ ks v *
            ((HeckeEigensystem.cNorm v)⁻¹ *
              ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).2) ^ js v) →
      ∀ (I : ℝ → ℂ) (R₀ : ℝ),
        (∀ R : ℝ, R₀ ≤ R →
          I R = κ * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
            (g ⟨τ e t, hτX e t⟩ * a e i j t) *
              (c * ( P e i j t * (2 * (R : ℂ))
                    - Q e i j t
                    + U e i j t * Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
                    - V e i j t * Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ)) ))) →
        Filter.Tendsto (fun R : ℝ => I R - (R : ℂ) * s g) Filter.atTop
          (nhds ((∑' n, cs n * g ⟨tabs n, htabs n⟩) + Λ g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz.solution
