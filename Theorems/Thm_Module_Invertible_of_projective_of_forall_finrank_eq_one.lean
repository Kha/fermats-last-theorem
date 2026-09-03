import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Invertible_of_projective_of_forall_finrank_eq_one

universe u v

theorem Module.Invertible.of_projective_of_forall_finrank_eq_one
    {A : Type u} [CommRing A] (P : Type v) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P]
    (h : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = 1) :
    Module.Invertible A P := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_of_projective_of_forall_finrank_eq_one.solution
