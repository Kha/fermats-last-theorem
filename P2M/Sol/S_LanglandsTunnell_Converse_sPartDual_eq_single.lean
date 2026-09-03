import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
namespace P2MW.S_LanglandsTunnell_Converse_sPartDual_eq_single

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell.Converse

theorem solution (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (n₀ : ↥S → ℤ)
    (hAd : ∀ n : ↥S → ℤ, n ≠ n₀ → Ad n = 0) :
    sPartDual K S Ad μ s = Ad n₀ * ∏ v : ↥S,
      ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n₀ v) := by
  unfold sPartDual
  rw [tsum_eq_single n₀ (fun n hn => by rw [hAd n hn, zero_mul])]
