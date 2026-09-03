import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_PrincipalLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_cuspKFiniteSubmodule_productionPinsOf_principalLevel_eq_levelOne

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.cuspKFiniteSubmodule_productionPinsOf_principalLevel_eq_levelOne
    (F : Type) [Field F] [NumberField F] (S : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F S
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ) :
    cuspKFiniteSubmodule F
        (productionPinsOf F S
          (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ =
      cuspKFiniteSubmodule F
        (productionPinsOf F S
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_cuspKFiniteSubmodule_productionPinsOf_principalLevel_eq_levelOne.solution
