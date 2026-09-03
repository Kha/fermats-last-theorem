import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_stable_submodule_inf_eq_bot_and_sub_mem_of_positive_skew_form

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_stable_submodule_inf_eq_bot_and_sub_mem_of_positive_skew_form
    (M N : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hNM : N ≤ M)
    (hM4 : (∀ w ∈ M, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M))
    (hM5 : (∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M))
    (hN4 : (∀ w ∈ N, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ N))
    (hN5 : (∀ w ∈ N, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ N))
    (B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ)
    (hB : (∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ M, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ M, ∀ w' ∈ M, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w')
    (P : ↥M →ₗ[ℂ] ↥M)
    (hPN : ∀ w : ↥M, (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ N → ((P w : ↥M) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ N)
    (hPP : ∀ w : ↥M, P (P w) = P w)
    (hPB : ∀ w w' : ↥M, B (P w) w' = B w (P w'))
    (hPfin : FiniteDimensional ℂ ↥(LinearMap.range P))
    (v : ↥M) (hPv : P v = v) :
    ∃ M' : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), M' ≤ M ∧
      (∀ w ∈ M', ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M') ∧
      (∀ w ∈ M', ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M') ∧
      M' ⊓ N = ⊥ ∧
      ∃ v' ∈ M', (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - v' ∈ N := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_stable_submodule_inf_eq_bot_and_sub_mem_of_positive_skew_form.solution
