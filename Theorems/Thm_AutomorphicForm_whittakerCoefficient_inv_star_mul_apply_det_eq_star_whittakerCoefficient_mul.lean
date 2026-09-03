import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import P2M.Util
import P2M.Sol.S_AutomorphicForm_whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem AutomorphicForm.whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul
    (K : Type) [Field K] [NumberField K] (pins : CarrierPins K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : ∀ x : AdeleRing (𝓞 K) K, ‖ψ x‖ = 1)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (χ : (AdeleRing (𝓞 K) K)ˣ → ℂ) (a : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ⁻¹ (fun h : AdelicGL2 (𝓞 K) K => (starRingEnd ℂ) (φ h) * χ (Matrix.GeneralLinearGroup.det h)) a g =
      (starRingEnd ℂ) (whittakerCoefficient K pins ψ φ a g) * χ (Matrix.GeneralLinearGroup.det g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul.solution
