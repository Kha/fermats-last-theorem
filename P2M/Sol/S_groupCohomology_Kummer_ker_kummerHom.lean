import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_kummerClass_eq_zero_iff
import P2M.Util
namespace P2MW.S_groupCohomology_Kummer_ker_kummerHom

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] (p : ℕ) :
    (kummerHom K L p).ker
      = ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf (powerSubgroup K L p) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, kummerHom_apply, ofAdd_eq_one,
    kummerClass_eq_zero_iff]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb⟩⟩
