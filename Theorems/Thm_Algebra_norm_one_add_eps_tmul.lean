import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_norm_one_add_eps_tmul

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem Algebra.norm_one_add_eps_tmul
    (A' B : Type u) [CommRing A'] [CommRing B] [Algebra A' B] [Module.Free A' B] [Module.Finite A' B] (f : B) :
    Algebra.norm (DualNumber A') ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f) =
      1 + TrivSqZeroExt.inr (Algebra.trace A' B f) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_norm_one_add_eps_tmul.solution
