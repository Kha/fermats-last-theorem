import Definitions.Def_NumberField_IdeleProductMeasure
import P2M.Util
import P2M.Sol.S_NumberField_Idele_integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem NumberField.Idele.integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (PZ : UnramifiedWhittaker.ProductMeasureData S νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K S)
    (d : Kˣ)

    (u : Kˣ) (hu1 : (u : K) ≠ 1)

    (IW : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (IU : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (B : (AdeleRing (𝓞 K) K)ˣ → ℂ)

    (IT : HeightOneSpectrum (𝓞 K) → ℤ → ℂ)
    (hWloc : ∀ v ∈ T, ∀ w : (AdeleRing (𝓞 K) K)ˣ, w ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) →
      IW w v = IT v (NumberField.Idele.ord K v w))

    (hUloc : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → ∀ w : (AdeleRing (𝓞 K) K)ˣ,
      IU w v = if ‖(((w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 ∧ ‖algebraMap K (v.adicCompletion K) (u : K)‖ = 1
        then (((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ))⁻¹ else 0)

    (hBloc : ∀ w : (AdeleRing (𝓞 K) K)ˣ, w ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) →
      B w = B (NumberField.Idele.partAt K S w))

    (hBint : Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * B zS) PZ.νS)

    (hITsum : ∀ v ∈ T, Summable fun e : ℤ =>
      ‖((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT v e‖) :
    ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∏ v ∈ T, IW (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d)) v) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S ∪ T), IU (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d)) v) *
          B (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d))) ∂νZK =
      (PZ.c : ℂ) *
        (if ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0
          then (1 : ℂ) else 0) *
        (if h1 : (u : K) - 1 ≠ 0 then
            ((NumberField.TateGlobal.ideleNorm K
                (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
          else 0) *
        (∏ v ∈ T, ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) *
            ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e *
              IT v e) *
        ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * B zS ∂PZ.νS := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral.solution
