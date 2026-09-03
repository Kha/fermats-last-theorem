import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_sigmaTensor_apply_eq_self_iff

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.sigmaTensor_apply_eq_self_iff
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L)
    (hfix : ∀ x : L, σ x = x → x ∈ (algebraMap K L).range) (a : L ⊗[K] A) :
    sigmaTensor K L A σ a = a ↔
      a ∈ Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_sigmaTensor_apply_eq_self_iff.solution
