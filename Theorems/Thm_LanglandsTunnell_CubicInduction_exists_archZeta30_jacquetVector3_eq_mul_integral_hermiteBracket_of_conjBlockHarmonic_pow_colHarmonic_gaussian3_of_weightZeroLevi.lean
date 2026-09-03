import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
attribute [-simp] LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell open LanglandsTunnell.CubicInduction hiding jacquetVector3_iotaGL_diagUnitGL2_mul exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3 open MeasureTheory

theorem LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_integral_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (m : ℕ) (hm : 1 ≤ m)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ m) * gaussian3 M)
    (u₁ u₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c u₂ c)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      0 < κ ∧
      archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
        (κ : ℂ) * (2 * (Real.pi : ℂ) * (a : ℂ) ^ m) *
          ∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
            ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
              ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (m + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ y₂ *
                (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
                D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) *
                ((∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ a₃.val * (-1 : ℂ) ^ c.val * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ (e : ZMod 2).val * (-1 : ℂ) ^ c.val * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ (e : ZMod 2).val * (-1 : ℂ) ^ a₃.val * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi.solution
