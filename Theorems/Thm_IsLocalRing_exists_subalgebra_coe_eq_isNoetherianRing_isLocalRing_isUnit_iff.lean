import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff

set_option autoImplicit false

universe u

theorem IsLocalRing.exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
    {A₀ : Type u} [CommRing A₀] {R : Type u} [CommRing R] [IsLocalRing R] [Algebra A₀ R]
    (T : Subalgebra A₀ R) [IsNoetherianRing ↥T] :
    ∃ S : Subalgebra A₀ R,
      (S : Set R) = {x : R | ∃ t ∈ T, ∃ u ∈ T, u ∉ IsLocalRing.maximalIdeal R ∧ x * u = t} ∧
      IsNoetherianRing ↥S ∧ IsLocalRing ↥S ∧ ∀ x : ↥S, IsUnit x ↔ IsUnit (x : R) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff.solution
