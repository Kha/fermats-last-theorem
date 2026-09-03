import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_AutomorphicForm_archCasimirAt_eq_raising_lowering_of_isArchSmoothAt
import Theorems.Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
import P2M.Util
namespace P2MW.S_AutomorphicForm_archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

noncomputable section

namespace Ws23
namespace M5

p2m_open "NumberField NumberField.InfinitePlace.NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

theorem archDerivAt_zero (d : ArchDir) : archDerivAt hw d (0 : AdelicGL2 (𝓞 F) F → ℂ) = 0 :=
  archDerivAt_const hw d 0

theorem main
        (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) (k : ℤ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hL : archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0) :
    archCasimirAt hw φ = (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • φ := by
  have hM2 := AutomorphicForm.archCasimirAt_eq_raising_lowering_of_isArchSmoothAt F hw φ hφ
  have hW := AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt F w hw k φ hφ hk
  rw [hL] at hM2
  rw [hM2]
  funext g
  have hWg := congrFun hW g
  have hWE := congrFun (congrArg (archDerivAt hw .E) hW) g
  have hWF := congrFun (congrArg (archDerivAt hw .Fm) hW) g
  rw [archDerivAt_smul] at hWE hWF
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hWg hWE hWF
  simp only [archDerivAt_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
    hWE, hWF]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-(Complex.I / 2) + (1 / 4 : ℂ) * (Complex.I * k)) * hWg +
    ((1 / 4 : ℂ) * (k : ℂ) ^ 2 * φ g - (1 / 2 : ℂ) * (k : ℂ) * φ g) * hI2

end Ws23.M5

end

theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) (k : ℤ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hL : archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0) :
    archCasimirAt hw φ = (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • φ :=
  Ws23.M5.main hw φ hφ k hk hL
