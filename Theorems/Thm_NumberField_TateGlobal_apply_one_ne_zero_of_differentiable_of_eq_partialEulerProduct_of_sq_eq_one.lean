import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal AutomorphicForm
open scoped Classical in

theorem NumberField.TateGlobal.apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ) (hχc : Continuous χ)
    (hχu : IsUnitaryChar (𝓞 K) K χ) (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLE : ∀ s : ℂ, 1 < s.re →
      L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    L 1 ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one.solution
