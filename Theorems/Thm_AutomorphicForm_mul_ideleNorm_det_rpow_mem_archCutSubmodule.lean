import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mul_ideleNorm_det_rpow_mem_archCutSubmodule

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.mul_ideleNorm_det_rpow_mem_archCutSubmodule
    (K : Type) [Field K] [NumberField K] (tysK : ArchTypeFamily K) (w : ℝ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : φ ∈ archCutSubmodule K tysK) :
    (fun g : AdelicGL2 (𝓞 K) K => φ g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ)) ∈ archCutSubmodule K tysK := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mul_ideleNorm_det_rpow_mem_archCutSubmodule.solution
