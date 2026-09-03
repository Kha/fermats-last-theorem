import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace

set_option autoImplicit false

universe u

theorem Algebra.not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]
    (P : Ideal B) [P.IsPrime] :
    ¬ ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L) ≤ P) ↔
      ∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace.solution
