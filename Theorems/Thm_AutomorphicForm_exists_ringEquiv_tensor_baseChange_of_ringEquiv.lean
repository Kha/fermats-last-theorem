import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_ringEquiv_tensor_baseChange_of_ringEquiv

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_ringEquiv_tensor_baseChange_of_ringEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (A' : Type) [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    (e : A ≃+* A') (he : Continuous e) (he' : Continuous e.symm) :
    letI : Algebra K A' := (e.toRingHom.comp (algebraMap K A)).toAlgebra
    ∃ E : L ⊗[K] A ≃+* L ⊗[K] A',
      Continuous E ∧ Continuous E.symm ∧
      (∀ (x : L) (a : A), E (x ⊗ₜ a) = x ⊗ₜ e a) ∧
      (∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K L A' σ (E z)) ∧
      (∀ g : GL (Fin 2) A, Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L A g) =
        toTensorGL K L A' (Matrix.GeneralLinearGroup.map e.toRingHom g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_ringEquiv_tensor_baseChange_of_ringEquiv.solution
