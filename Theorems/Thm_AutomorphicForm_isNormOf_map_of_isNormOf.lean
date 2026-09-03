import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isNormOf_map_of_isNormOf

set_option autoImplicit false

open scoped TensorProduct

theorem AutomorphicForm.isNormOf_map_of_isNormOf
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (A B : Type) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (g : A →ₐ[K] B)
    (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ γ δ) :
    AutomorphicForm.IsNormOf K L B σ (Matrix.GeneralLinearGroup.map g.toRingHom γ)
      (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.map (AlgHom.id K L) g).toRingHom δ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isNormOf_map_of_isNormOf.solution
