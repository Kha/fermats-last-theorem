import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_ArchSpherical
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isLevelSphericalOfType_ofChar_flat
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField IsDedekindDomain
open NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.CuspidalSpectrum

theorem AutomorphicForm.isLevelSphericalOfType_ofChar_flat
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ‖((χ w k : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 F)) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsLevelSphericalOfType F (ArchTypeFamily.ofChar F χ)
      (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) f) :
    IsLevelSphericalOfType F (ArchTypeFamily.ofChar F χ)
      (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (flat F σ f) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isLevelSphericalOfType_ofChar_flat.solution
