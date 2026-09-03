import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOfGamma1_isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.IsAdelicLiftOfGamma1.isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hε : CuspForm.HasNebentypus ε h)
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ AdelicDock.ratLevel M) (c : ℂ)
    (hT : ModularForm.heckeU 2 (Ideal.absNorm v.asIdeal) ⇑h
          + ε ((Ideal.absNorm v.asIdeal : ℕ) : ZMod M) •
              ((⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix (Ideal.absNorm v.asIdeal))
        = c • ⇑h) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt ℚ ((productionPinsGeneral ℚ).U (AdelicDock.ratLevel M))
      ((productionPinsGeneral ℚ).gen v) v Φ c := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOfGamma1_isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq.solution
