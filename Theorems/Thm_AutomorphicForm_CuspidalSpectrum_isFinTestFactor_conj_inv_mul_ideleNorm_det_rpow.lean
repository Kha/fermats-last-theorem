import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
open scoped ComplexConjugate

theorem AutomorphicForm.CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    IsFinTestFactor F (fun b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => conj (ff b⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F b)) ^ (-σ) : ℝ) : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow.solution
