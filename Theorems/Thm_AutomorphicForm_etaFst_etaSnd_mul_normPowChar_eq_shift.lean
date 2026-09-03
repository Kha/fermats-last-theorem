import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_NormPowChar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_etaFst_etaSnd_mul_normPowChar_eq_shift

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm

theorem AutomorphicForm.etaFst_etaSnd_mul_normPowChar_eq_shift
    (K : Type) [Field K] [NumberField K]
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (_hαI : ∀ x, ((α x : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm K x)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : ℝ) (s : ℂ) :
    etaFst (χ * NumberField.TateGlobal.normPowChar K τ) α hα s = etaFst χ α hα (s + (τ : ℂ) * Complex.I) ∧
    etaFst (χ * (NumberField.TateGlobal.normPowChar K τ)⁻¹) α hα s = etaFst χ α hα (s - (τ : ℂ) * Complex.I) ∧
    etaSnd (χ * NumberField.TateGlobal.normPowChar K τ) α hα s = etaSnd χ α hα (s - (τ : ℂ) * Complex.I) ∧
    etaSnd (χ * (NumberField.TateGlobal.normPowChar K τ)⁻¹) α hα s = etaSnd χ α hα (s + (τ : ℂ) * Complex.I) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_etaFst_etaSnd_mul_normPowChar_eq_shift.solution
