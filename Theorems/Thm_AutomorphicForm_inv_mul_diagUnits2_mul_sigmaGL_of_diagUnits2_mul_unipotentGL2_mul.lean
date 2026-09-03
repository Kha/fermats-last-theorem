import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul
    (K L A : Type) [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (α β a₁ a₂ : (L ⊗[K] A)ˣ) (ξ : L ⊗[K] A) (k : GL (Fin 2) (L ⊗[K] A)) :
    (diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ * k)⁻¹ * diagUnits2 α β *
        AutomorphicForm.sigmaGL K L A σ (diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ * k) =
      k⁻¹ *
        (diagUnits2 (α * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₁ * a₁⁻¹)
            (β * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₂ * a₂⁻¹) *
          AutomorphicForm.unipotentGL2
            (AutomorphicForm.sigmaTensor K L A σ ξ -
              (((β * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₂ * a₂⁻¹) *
                  (α * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₁ * a₁⁻¹)⁻¹ : (L ⊗[K] A)ˣ) :
                L ⊗[K] A) * ξ)) *
        AutomorphicForm.sigmaGL K L A σ k := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul.solution
