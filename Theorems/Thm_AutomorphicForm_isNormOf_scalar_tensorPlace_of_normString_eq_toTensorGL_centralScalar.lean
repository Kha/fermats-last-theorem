import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isNormOf_scalar_tensorPlace_of_normString_eq_toTensorGL_centralScalar

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.isNormOf_scalar_tensorPlace_of_normString_eq_toTensorGL_centralScalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom) u))
      (AutomorphicForm.tensorPlace K L v δ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isNormOf_scalar_tensorPlace_of_normString_eq_toTensorGL_centralScalar.solution
