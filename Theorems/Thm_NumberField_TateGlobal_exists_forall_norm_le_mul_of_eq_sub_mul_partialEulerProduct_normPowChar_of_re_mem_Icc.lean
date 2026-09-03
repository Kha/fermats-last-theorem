import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_NormPowChar
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical in

theorem NumberField.TateGlobal.exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc
    (K : Type) [Field K] [NumberField K] (τ : ℝ) (T : Finset (HeightOneSpectrum (𝓞 K))) (σ₁ σ₂ : ℝ)
    (Q : ℂ → ℂ) (_hQ : Differentiable ℂ Q)
    (_hQE : ∀ s : ℂ, 1 < s.re →
      Q s = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt (normPowChar K τ) v.1 then
                (((normPowChar K τ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ‖Q w‖ ≤ A * (1 + |w.im|) ^ N := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc.solution
