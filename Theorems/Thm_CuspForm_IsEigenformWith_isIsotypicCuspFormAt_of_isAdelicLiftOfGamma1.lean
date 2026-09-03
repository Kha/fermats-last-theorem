import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_CuspForm_IsEigenformWith_isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem CuspForm.IsEigenformWith.isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (hξ : ∀ (z : ↥((productionPinsGeneral ℚ).Z)) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      Φ (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * x) = ((ξ z : ℂˣ) : ℂ) * Φ x)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ AdelicDock.ratLevel M)
    (Ψ : HeckeEigensystem ℚ ℂ)
    (ha : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Ψ.a v = ModularFormClass.qCoeff h (Ideal.absNorm v.asIdeal))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Ψ.b v = (Ideal.absNorm v.asIdeal : ℂ) * ε ((Ideal.absNorm v.asIdeal : ℕ) : ZMod M)) :
    IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ (AdelicDock.ratLevel M) S Ψ Φ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsEigenformWith_isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1.solution
