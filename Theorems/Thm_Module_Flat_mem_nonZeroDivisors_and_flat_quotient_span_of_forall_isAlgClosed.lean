import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_Module_Flat_mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed

set_option autoImplicit false

universe u v

open TensorProduct nonZeroDivisors

theorem Module.Flat.mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing B]
    [Module.Flat A B] (g : B)
    (hg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra A K],
      (g ⊗ₜ[A] (1 : K)) ∈ nonZeroDivisors (B ⊗[A] K)) :
    g ∈ nonZeroDivisors B ∧ Module.Flat A (B ⧸ Ideal.span {g}) := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed.solution
