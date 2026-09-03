import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing

set_option autoImplicit false

universe u v w

theorem Algebra.Etale.algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (E : Type v) [CommRing E] [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
    (B : Type w) [CommRing B] [Algebra R B] [Module.Finite R B]
    (φ ψ : E →ₐ[R] B)
    (h : ∀ x : E, φ x - ψ x ∈ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) :
    φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing.solution
