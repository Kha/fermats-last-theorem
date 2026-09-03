import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors
theorem NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F]
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ (s : Finset F) (c : F → ℂ),
      h = ∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles.solution
