import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_isBoundedGenuineFn_productionPinsGeneral_stdAddChar
import Theorems.Thm_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one
import P2M.Util
namespace P2MW.S_CuspForm_IsAdelicLiftOf_isBoundedGenuineFn_productionPinsGeneral_stdAddChar

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : CuspForm.IsAdelicLiftOf g Φ) :
    IsBoundedGenuineFn ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) Φ := by
  obtain ⟨g₁, hcoe, -⟩ := CuspForm.exists_gamma1_coe_eq_and_hasNebentypus_one (M := M) 2 g
  have hΦ₁ : CuspForm.IsAdelicLiftOfGamma1 g₁ Φ := by
    refine ⟨hΦ.1, hΦ.2.1, fun h hfin hpos => ?_⟩
    rw [hcoe]
    exact hΦ.2.2 h hfin hpos
  exact CuspForm.IsAdelicLiftOfGamma1.isBoundedGenuineFn_productionPinsGeneral_stdAddChar Φ hΦ₁
