import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
theorem LanglandsTunnell.exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd
    (F : Type) [Field F] [NumberField F]
    (N : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
      HeckeIntegralSeam.IsHeckeCosetSystem ((productionPinsGeneral F).U N)
        ((productionPinsGeneral F).gen v) reps := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd.solution
