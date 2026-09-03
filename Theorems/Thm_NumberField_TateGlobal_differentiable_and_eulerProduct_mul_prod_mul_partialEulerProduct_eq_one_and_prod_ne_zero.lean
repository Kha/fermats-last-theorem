import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_NormPowChar
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_differentiable_and_eulerProduct_mul_prod_mul_partialEulerProduct_eq_one_and_prod_ne_zero

set_option autoImplicit false

p2m_open "NumberField~multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one IsDedekindDomain AutomorphicForm"
p2m_open "NumberField.TateGlobal~localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt"
open scoped Classical

theorem NumberField.TateGlobal.differentiable_and_eulerProduct_mul_prod_mul_partialEulerProduct_eq_one_and_prod_ne_zero
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v) :
    let P : ℂ → ℂ := fun w => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
    let FS : ℂ → ℂ := fun w => ∏ v ∈ S,
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))
    Differentiable ℂ FS ∧
    (∀ w : ℂ, 1 < w.re →
      P w * FS w * (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))) = 1) ∧
    (∀ w : ℂ, 0 < w.re →
      FS w ≠ 0 ∧ (∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-w.re))) ≤ ‖FS w‖) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_differentiable_and_eulerProduct_mul_prod_mul_partialEulerProduct_eq_one_and_prod_ne_zero.solution
