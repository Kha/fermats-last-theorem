import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_trace_baseChange_one_tmul
open scoped TensorProduct

theorem Algebra.trace_baseChange_one_tmul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (S : Type*) [CommRing S] [Algebra A S]
    [Module.Free A B] [Module.Finite A B] (x : B) :
    Algebra.trace S (TensorProduct A S B) (1 ⊗ₜ[A] x) = algebraMap A S (Algebra.trace A B x) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_trace_baseChange_one_tmul.solution
