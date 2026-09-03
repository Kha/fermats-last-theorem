import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_fnTwist_gaussSumFn
attribute [-simp] AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed
open NumberField AutomorphicForm AutomorphicForm.SmoothCusp IsDedekindDomain NumberField.AdelicLevel

theorem LanglandsTunnell.isHeckeCosetEigenfunctionAt_fnTwist_gaussSumFn
    (F : Type) [Field F] [NumberField F]
    (N : Ideal (𝓞 F))
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {av : ℂ} (v : HeightOneSpectrum (𝓞 F))
    (hvdvd : ¬ v.asIdeal ∣ N * 𝔣 ^ 2)
    (hinv : ∀ g, ∀ u ∈ (productionPinsCompact F).U N, φ (g * u) = φ g)
    (heig : IsHeckeCosetEigenfunctionAt F ((productionPinsCompact F).U N)
      (heckeGen (𝓞 F) F v) v φ av) :
    IsHeckeCosetEigenfunctionAt F ((productionPinsCompact F).U (N * 𝔣 ^ 2))
      (heckeGen (𝓞 F) F v) v (fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ))
      (((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) * av) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_fnTwist_gaussSumFn.solution
