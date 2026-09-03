import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_heckeCosetSystem_productionPinsCompact_of_not_dvd
attribute [-instance] HeckeIntegralSeam.finite_padicInt_quotient_span_p
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
theorem LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd
    (N : Ideal (𝓞 ℚ)) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ,
      HeckeIntegralSeam.IsHeckeCosetSystem ((productionPinsCompact ℚ).U N)
        ((productionPinsCompact ℚ).gen v) reps := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_heckeCosetSystem_productionPinsCompact_of_not_dvd.solution
