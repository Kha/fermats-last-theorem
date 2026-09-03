import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isReduced_of_forall_exists_derivation_of_charZero

set_option autoImplicit false

theorem IsLocalRing.isReduced_of_forall_exists_derivation_of_charZero
    (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]
    (hk : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    (hder : ∀ φ : A →ₗ[k] k, (∀ a ∈ (IsLocalRing.maximalIdeal A) ^ 2, φ a = 0) → (∀ c : k, φ (algebraMap k A c) = 0) →
      ∃ D : Derivation k A A, ∀ a : A, D a - algebraMap k A (φ a) ∈ IsLocalRing.maximalIdeal A) :
    IsReduced A := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isReduced_of_forall_exists_derivation_of_charZero.solution
