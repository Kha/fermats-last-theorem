import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.exists_notMem_forall_dual_eq_trace_iff_fiber
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (P' : Ideal (p.Fiber B)) [P'.IsPrime]
    (hP' : P = P'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    (∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y)) ↔
      (∃ s ∉ P', ∀ φ : Module.Dual p.ResidueField (p.Fiber B), ∃ x : p.Fiber B, ∀ y : p.Fiber B,
        φ (s * y) = Algebra.trace p.ResidueField (p.Fiber B) (x * y)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber.solution
