import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_exists_isIdempotentElem_map_eq_of_module_finite

set_option autoImplicit false

universe u v

theorem HenselianLocalRing.exists_isIdempotentElem_map_eq_of_module_finite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {B : Type v} [CommRing B] [Algebra R B] [Module.Finite R B]
    (e₀ : B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) (he₀ : IsIdempotentElem e₀) :
    ∃ e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk (Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) e = e₀ := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_exists_isIdempotentElem_map_eq_of_module_finite.solution
