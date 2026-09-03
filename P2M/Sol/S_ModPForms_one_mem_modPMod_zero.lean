import Mathlib
import Definitions.Def_CuspForm_ModPForms
import P2M.Util
namespace P2MW.S_ModPForms_one_mem_modPMod_zero

set_option autoImplicit false

open UpperHalfPlane

theorem solution (N : ℕ) (F : Type) [Field F] :
    (1 : PowerSeries F) ∈ ModPForms.modPMod N 0 F := by
  unfold ModPForms.modPMod
  refine Submodule.subset_span ⟨(1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0),
    fun n => if n = 0 then 1 else 0, fun n => ?_, ?_⟩
  · unfold ModularFormClass.qCoeff
    rw [ModularForm.qExpansion_one, PowerSeries.coeff_one]
    by_cases hn : n = 0 <;> simp [hn]
  · ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    by_cases hn : n = 0 <;> simp [hn]
