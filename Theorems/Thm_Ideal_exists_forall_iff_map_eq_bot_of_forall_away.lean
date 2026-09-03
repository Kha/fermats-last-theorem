import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_forall_iff_map_eq_bot_of_forall_away

set_option autoImplicit false
universe u

theorem Ideal.exists_forall_iff_map_eq_bot_of_forall_away
    (A : Type u) [CommRing A]
    (P : ∀ (A' : Type u) [CommRing A'], (A →+* A') → Prop)
    (hPmap : ∀ (A' A'' : Type u) [CommRing A'] [CommRing A''] (χ : A' →+* A'') (φ : A →+* A'),
      P A' φ → P A'' (χ.comp φ))
    (hPloc : ∀ (A' : Type u) [CommRing A'] (φ : A →+* A') (κ : Type u) (s : κ → A'),
      Ideal.span (Set.range s) = ⊤ →
      (∀ k, P (Localization.Away (s k)) ((algebraMap A' (Localization.Away (s k))).comp φ)) → P A' φ)
    (κ : Type u) (r : κ → A) (hr : Ideal.span (Set.range r) = ⊤)
    (K : ∀ i : κ, Ideal (Localization.Away (r i)))
    (hK : ∀ (i : κ) (A' : Type u) [CommRing A'] (χ : Localization.Away (r i) →+* A'),
      P A' (χ.comp (algebraMap A (Localization.Away (r i)))) ↔ Ideal.map χ (K i) = ⊥) :
    ∃ I : Ideal A, ∀ (A' : Type u) [CommRing A'] (φ : A →+* A'), P A' φ ↔ Ideal.map φ I = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_forall_iff_map_eq_bot_of_forall_away.solution
