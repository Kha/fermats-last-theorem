import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Grassmannian_exists_chart_equiv_algHom_symmetricAlgebra_quotient

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Grassmannian.exists_chart_equiv_algHom_symmetricAlgebra_quotient
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) (x : Fin k → M) :
    ∃ (J : Ideal (SymmetricAlgebra R (Fin k → M)))
      (_ : J = Ideal.span {a | ∃ i j : Fin k,
        a = SymmetricAlgebra.ι R (Fin k → M) (Pi.single i (x j)) - if i = j then 1 else 0})
      (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)} ≃
          (SymmetricAlgebra R (Fin k → M) ⧸ J →ₐ[R] A)),
      (∀ (A : Type) [CommRing A] [Algebra R A]
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (m : M),
          ∑ i, pt A N (Ideal.Quotient.mk J (SymmetricAlgebra.ι R (Fin k → M) (Pi.single i m))) •
              N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
            N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) ∧
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}),
          ∃ h : Function.Bijective fun v : Fin k → B =>
              ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i),
            pt B ⟨Module.Grassmannian.map φ N.1, h⟩ = φ.comp (pt A N)) := by p2m_exact_reverting @_root_.P2MW.S_Module_Grassmannian_exists_chart_equiv_algHom_symmetricAlgebra_quotient.solution
