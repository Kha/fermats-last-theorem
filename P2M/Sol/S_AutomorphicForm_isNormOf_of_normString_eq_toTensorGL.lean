import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
namespace P2MW.S_AutomorphicForm_isNormOf_of_normString_eq_toTensorGL

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) (ε : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.normString K L A σ ε = AutomorphicForm.toTensorGL K L A γ) :
    AutomorphicForm.IsNormOf K L A σ γ ε := by
  refine ⟨1, ?_⟩
  show AutomorphicForm.toTensorGL K L A γ = 1⁻¹ * AutomorphicForm.normString K L A σ ε * 1
  rw [inv_one, one_mul, mul_one, h]

#print axioms solution
