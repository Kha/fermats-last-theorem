import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (hodd : Module.finrank K L ≠ 2)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : (L ⊗[K] v.adicCompletion K)ˣ,
      AutomorphicForm.normString K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (AdelicLevel.finComponent (𝓞 K) K v
            (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))) :
    ∃ z : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
          (AutomorphicForm.centralScalar (𝓞 K) K u) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two.solution
