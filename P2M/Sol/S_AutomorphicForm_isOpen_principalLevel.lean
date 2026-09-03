import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import P2M.Util
namespace P2MW.S_AutomorphicForm_isOpen_principalLevel

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) :
    IsOpen ((principalLevel (𝓞 F) F N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := by
  have h1 : IsOpen (levelOne (𝓞 F) F N : Set (AdelicGL2 (𝓞 F) F)) := isOpen_levelOne (𝓞 F) F hN
  have h2 : IsOpen ((fun g => (weyl (𝓞 F) F)⁻¹ * g * weyl (𝓞 F) F) ⁻¹' (levelOne (𝓞 F) F N : Set (AdelicGL2 (𝓞 F) F))) :=
    h1.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  convert h1.inter h2 using 1
  ext g
  simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  rw [mem_principalLevel_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
