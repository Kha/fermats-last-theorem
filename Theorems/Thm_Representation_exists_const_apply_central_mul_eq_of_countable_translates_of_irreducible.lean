import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_const_apply_central_mul_eq_of_countable_translates_of_irreducible

set_option autoImplicit false

theorem Representation.exists_const_apply_central_mul_eq_of_countable_translates_of_irreducible
    {G : Type*} [Group G] (f : G → ℂ)
    (hcount : (Set.range fun h : G => fun g : G => f (g * h)).Countable)
    (hf : f ≠ 0)
    (hirr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => f (g * h)),
      w ≠ 0 → f ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)))
    (z : G) (hz : ∀ g : G, z * g = g * z) :
    ∃ c : ℂ, ∀ g : G, f (z * g) = c * f g := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_const_apply_central_mul_eq_of_countable_translates_of_irreducible.solution
