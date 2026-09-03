import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal

theorem
LanglandsTunnell.CubicInduction.localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq
    (v : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 v → ℂ)
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (hE : E ≠ 0) (hEd : Ed ≠ 0)
    (R₁ R₂ : Polynomial ℂ) (m : ℤ)
    (hA : R₁ ≠ 0 ∧ R₂ ≠ 0 ∧
      ∀ g : LocalGL3 v,
        letI := localBorel ℚ v
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g *
              Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt
            ℚ v) (dualWhittakerFn3 W) 1⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g *
              (Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) =
            R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s)))
    (hB : ∀ s : ℂ,
      R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) *
          Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
        ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
          R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))
    :
    ∀ g : LocalGL3 v,
    (letI := localBorel ℚ v
     ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
      (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
        P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
          (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
      ∀ s : ℂ, σ₁ < (1 - s).re →
        localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
            W 1 (1 - s) g =
          (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
            ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq.solution
