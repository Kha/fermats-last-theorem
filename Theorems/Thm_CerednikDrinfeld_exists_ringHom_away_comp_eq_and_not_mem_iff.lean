import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff

set_option autoImplicit false

theorem CerednikDrinfeld.exists_ringHom_away_comp_eq_and_not_mem_iff
    {B B' : Type} [CommRing B] [CommRing B'] (f : B →+* B') (g : B) :
    (∃ fg : Localization.Away g →+* Localization.Away (f g),
        fg.comp (algebraMap B (Localization.Away g)) = (algebraMap B' (Localization.Away (f g))).comp f) ∧
      ∀ x' : PrimeSpectrum B', f g ∉ x'.asIdeal ↔ g ∉ (PrimeSpectrum.comap f x').asIdeal := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff.solution
