import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_jacquetIntegral_principalSeries2_smooth_law_central_flip

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.jacquetIntegral_principalSeries2_smooth_law_central_flip
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : ((w₀p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (d : GL (Fin 2) (p.adicCompletion ℚ)) (hd : ((d : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, 0; 0, -1]) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p

    (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φ (g * k) = φ g) ∧

    IsLocallyConstant (fun k : GL (Fin 2) (p.adicCompletion ℚ) => (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧

    (∀ (a : (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (unipotent a * k)) ∂(selfDualHaarAt ℚ p)) = NumberField.StandardAddChar.psiLocal ℚ p (-a) * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧
    (∀ (a : (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (unipotentGL2 a * k)) ∂(selfDualHaarAt ℚ p)) = (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ a * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧

    (∀ (zc : (p.adicCompletion ℚ)ˣ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
      (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * k)) ∂(selfDualHaarAt ℚ p)) = ((μ 0 zc : ℂˣ) : ℂ) * ((μ 1 zc : ℂˣ) : ℂ) * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧

    (∀ (t : (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) (d * (unipotent t * k)))) ∂(selfDualHaarAt ℚ p)) = NumberField.StandardAddChar.psiLocal ℚ p (-t) * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) (d * k))) ∂(selfDualHaarAt ℚ p))) ∧
    IsLocallyConstant (fun k : GL (Fin 2) (p.adicCompletion ℚ) => (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) (d * k))) ∂(selfDualHaarAt ℚ p))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetIntegral_principalSeries2_smooth_law_central_flip.solution
