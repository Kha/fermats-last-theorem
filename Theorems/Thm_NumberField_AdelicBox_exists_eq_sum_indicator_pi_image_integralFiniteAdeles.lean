import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles

set_option autoImplicit false

open NumberField NumberField.AdelicBox IsDedekindDomain

theorem NumberField.AdelicBox.exists_eq_sum_indicator_pi_image_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    {h : (ι → FiniteAdeleRing (𝓞 F) F) → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ),
      h = ∑ k ∈ s, c k •
        (Set.pi Set.univ fun i => (fun z : FiniteAdeleRing (𝓞 F) F ↦
            algebraMap F (FiniteAdeleRing (𝓞 F) F) (k i)
              + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles.solution
