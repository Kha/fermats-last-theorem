import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2
import Theorems.Thm_groupCohomology_Cores_cores_map_res_eq_index_smul
import P2M.Util
namespace P2MW.S_groupCohomology_eq_zero_of_map_res_two_eq_zero_of_coprime

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H : Subgroup G) [H.FiniteIndex]
    {p n : ℕ} (hcop : H.index.Coprime p) (x : H2 A) (hp : p ^ n • x = 0)
    (hres : (map H.subtype (𝟙 (Rep.res H.subtype A)) 2).hom x = 0) : x = 0 := by
  obtain ⟨τ⟩ := groupCohomology.Cores.Transversal.nonempty (H := H)
  have h1 : H.index • x = 0 := by rw [← groupCohomology.Cores.cores_map_res_eq_index_smul A H τ x, hres, map_zero]
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 (hcop.pow_right n)
  have := congrArg (fun c : ℤ => c • x) hab
  simp only [add_smul, mul_smul, one_smul] at this
  rw [← this, natCast_zsmul, natCast_zsmul, h1, hp, smul_zero, smul_zero, add_zero]
