import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isNormOf_of_normString_eq_toTensorGL

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.isNormOf_of_normString_eq_toTensorGL
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) (ε : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.normString K L A σ ε = AutomorphicForm.toTensorGL K L A γ) :
    AutomorphicForm.IsNormOf K L A σ γ ε := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isNormOf_of_normString_eq_toTensorGL.solution
