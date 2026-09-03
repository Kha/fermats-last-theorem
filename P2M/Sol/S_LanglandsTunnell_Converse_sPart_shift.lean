import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
namespace P2MW.S_LanglandsTunnell_Converse_sPart_shift

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell.Converse

theorem solution (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (A : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (m : ↥S → ℤ) :
    (∏ v : ↥S,
        (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v)) *
      sPart K S A μ s = sPart K S (fun n => A (n - m)) μ s := by
  have hx : ∀ v : ↥S,
      (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ≠ 0 := by
    intro v
    refine mul_ne_zero (Units.ne_zero _) fun h => ?_
    have hq : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) = 0 := ((Complex.cpow_eq_zero_iff _ _).1 h).1
    have hq' : Ideal.absNorm v.1.asIdeal = 0 := by exact_mod_cast hq
    exact v.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 hq')
  have hz : ∀ (n : ↥S → ℤ) (v : ↥S),
      (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v + m v) =
      (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v) *
      (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v) :=
    fun n v => zpow_add₀ (hx v) (n v) (m v)
  unfold sPart
  rw [← tsum_mul_left]
  conv_rhs => rw [← (Equiv.addRight m).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, Pi.add_apply, hz, Finset.prod_mul_distrib]
  ring
