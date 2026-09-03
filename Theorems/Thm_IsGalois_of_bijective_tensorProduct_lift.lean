import Mathlib
import P2M.Util
import P2M.Sol.S_IsGalois_of_bijective_tensorProduct_lift

set_option autoImplicit false

open scoped TensorProduct

theorem IsGalois.of_bijective_tensorProduct_lift
    {K₁ K E F : Type*} [Field K₁] [Field K] [Field E] [Field F]
    [Algebra K₁ K] [FiniteDimensional K₁ K] [IsGalois K₁ K]
    [Algebra K₁ E] [Algebra E F] [Algebra K F] [Algebra K₁ F]
    [IsScalarTower K₁ E F] [IsScalarTower K₁ K F]
    (h : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId E F) (IsScalarTower.toAlgHom K₁ K F)
        (fun _ _ => Commute.all _ _) : E ⊗[K₁] K →ₐ[E] F)) :
    FiniteDimensional E F ∧ IsGalois E F ∧
      Nonempty ((F ≃ₐ[E] F) ≃* (K ≃ₐ[K₁] K)) ∧
      Module.finrank E F = Module.finrank K₁ K := by p2m_exact_reverting @_root_.P2MW.S_IsGalois_of_bijective_tensorProduct_lift.solution
