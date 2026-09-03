import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_of_isAdicComplete_of_forall_pow_maximalIdeal

set_option autoImplicit false

theorem Module.FaithfullyFlat.of_isAdicComplete_of_forall_pow_maximalIdeal
    (R B : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [IsLocalRing B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Algebra R B] [IsLocalHom (algebraMap R B)]
    (hinj : ∀ (n : ℕ) (r : R), algebraMap R B r ∈ IsLocalRing.maximalIdeal B ^ n → r ∈ IsLocalRing.maximalIdeal R ^ n)
    (hsurj : ∀ (n : ℕ) (b : B), ∃ r : R, b - algebraMap R B r ∈ IsLocalRing.maximalIdeal B ^ n) :
    Module.FaithfullyFlat R B := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_of_isAdicComplete_of_forall_pow_maximalIdeal.solution
