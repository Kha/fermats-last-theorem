import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Grassmannian_exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Grassmannian.exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) :
    ∃ P : ∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M),
        {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)} → (Fin k → M) → A,
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (m : M),
          ∑ i, P A x N (Function.update x i m) • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
            N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (y : Fin k → M),
          P A x N y = (Matrix.of fun i j => P A x N (Function.update x i (y j))).det) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}),
          P A x N x = 1) ∧
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}),
          ∃ h : Function.Bijective fun v : Fin k → B =>
              ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i),
            ∀ y : Fin k → M, P B x ⟨Module.Grassmannian.map φ N.1, h⟩ y = φ (P A x N y)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (y : Fin k → M),
          (Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] y i)) ↔ IsUnit (P A x N y)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (y : Fin k → M)
          (hy : Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] y i))
          (z : Fin k → M),
          P A x N z = P A x N y * P A y ⟨N.1, hy⟩ z) := by p2m_exact_reverting @_root_.P2MW.S_Module_Grassmannian_exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit.solution
