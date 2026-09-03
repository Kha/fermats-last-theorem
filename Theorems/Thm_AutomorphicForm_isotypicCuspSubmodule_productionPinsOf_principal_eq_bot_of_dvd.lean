import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_PrincipalLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (Dset : Set (AdelicGL2 (𝓞 F) F))
    (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F Dset (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (hvS : v ∉ S) (hv : v.asIdeal ∣ N) :
    isotypicCuspSubmodule F
      (productionPinsOf F Dset (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ N S Φ = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd.solution
