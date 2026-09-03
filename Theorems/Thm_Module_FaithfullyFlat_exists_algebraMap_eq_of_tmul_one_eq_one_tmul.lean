import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul

set_option autoImplicit false

universe u v

open TensorProduct

theorem Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {b : B} (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.solution
