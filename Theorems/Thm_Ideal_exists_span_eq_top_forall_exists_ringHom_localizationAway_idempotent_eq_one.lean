import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one

set_option autoImplicit false

open scoped BigOperators

theorem Ideal.exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one
    {S : Type} [CommRing S] {m : ℕ} (r : Fin m → S) (hr : Ideal.span (Set.range r) = ⊤)
    (k : Fin m → ℕ) (ε : ∀ a : Fin m, Fin (k a) → Localization.Away (r a))
    (hε₁ : ∀ a i, IsIdempotentElem (ε a i)) (hε₂ : ∀ a, ∑ i, ε a i = 1)
    (hε₃ : ∀ a i j, i ≠ j → ε a i * ε a j = 0) :
    ∃ (m' : ℕ) (t : Fin m' → S), Ideal.span (Set.range t) = ⊤ ∧
      ∀ b : Fin m', ∃ (a : Fin m) (i : Fin (k a)) (ρ : Localization.Away (r a) →+* Localization.Away (t b)),
        ρ.comp (algebraMap S (Localization.Away (r a))) = algebraMap S (Localization.Away (t b)) ∧
        ρ (ε a i) = 1 ∧ ∀ j : Fin (k a), j ≠ i → ρ (ε a j) = 0 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one.solution
