import Mathlib
import P2M.Util
import P2M.Sol.S_Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one

universe u

open TensorProduct

set_option autoImplicit false

theorem Module.finrank_baseChange_eq_one_of_rankAtStalk_eq_one
    {R : Type u} [CommRing R] (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Flat R P]
    (h : ∀ 𝔭, Module.rankAtStalk (R := R) P 𝔭 = 1)
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] P) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one.solution
