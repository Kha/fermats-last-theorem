import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_jointly_injective_isLocalHom_of_isReduced

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_jointly_injective_isLocalHom_of_isReduced
    (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsReduced T] :
    ∃ (n : ℕ) (A : Fin n → Type) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsDomain (A i))
      (_ : ∀ i, IsLocalRing (A i)) (_ : ∀ i, IsNoetherianRing (A i)) (χ : ∀ i, T →+* A i),
      (∀ i, IsLocalHom (χ i)) ∧ (∀ i, Function.Surjective (χ i)) ∧
        (∀ x : T, (∀ i, χ i x = 0) → x = 0) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_jointly_injective_isLocalHom_of_isReduced.solution
