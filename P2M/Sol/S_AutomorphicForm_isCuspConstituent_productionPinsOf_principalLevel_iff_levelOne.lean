import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_PrincipalLevel
import P2M.Util
namespace P2MW.S_AutomorphicForm_isCuspConstituent_productionPinsOf_principalLevel_iff_levelOne

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.CuspidalConstituent

theorem solution
    (F : Type) [Field F] [NumberField F] (S : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F S
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) :
    IsCuspConstituent F
        (productionPinsOf F S
          (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ V ↔
      IsCuspConstituent F
        (productionPinsOf F S
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ V := by

  have key : ∀ W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      IsCuspSubrep F
        (productionPinsOf F S
          (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ W ↔
      IsCuspSubrep F
        (productionPinsOf F S
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ W := by
    intro W
    constructor
    · intro h; exact ⟨h.le, h.rightTranslate_fin_mem, h.rightTranslate_arch_mem, h.rightConv_mem⟩
    · intro h; exact ⟨h.le, h.rightTranslate_fin_mem, h.rightTranslate_arch_mem, h.rightConv_mem⟩
  unfold IsCuspConstituent
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(key V).mp h1, h2, fun W hW hle => h3 W ((key W).mpr hW) hle⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(key V).mpr h1, h2, fun W hW hle => h3 W ((key W).mp hW) hle⟩
