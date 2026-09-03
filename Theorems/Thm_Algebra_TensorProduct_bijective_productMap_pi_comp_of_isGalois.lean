import Mathlib
import Definitions.Def_Mathlib_RightActionInstances
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois

set_option autoImplicit false

open scoped TensorProduct
theorem Algebra.TensorProduct.bijective_productMap_pi_comp_of_isGalois
    (K L F : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Field F] [Algebra K F] (σ₀ : L →ₐ[K] F) :
    Function.Bijective
      (Algebra.TensorProduct.productMap
        (Pi.algHom K (fun _ : L ≃ₐ[K] L => F) (fun τ : L ≃ₐ[K] L => σ₀.comp (τ : L →ₐ[K] L)))
        (Pi.algHom K (fun _ : L ≃ₐ[K] L => F) (fun _ : L ≃ₐ[K] L => AlgHom.id K F))) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois.solution
