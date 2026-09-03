import Mathlib
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff

set_option autoImplicit false

theorem solution
    {B B' : Type} [CommRing B] [CommRing B'] (f : B →+* B') (g : B) :
    (∃ fg : Localization.Away g →+* Localization.Away (f g),
        fg.comp (algebraMap B (Localization.Away g)) = (algebraMap B' (Localization.Away (f g))).comp f) ∧
      ∀ x' : PrimeSpectrum B', f g ∉ x'.asIdeal ↔ g ∉ (PrimeSpectrum.comap f x').asIdeal := by
  have hle : Submonoid.powers g ≤ (Submonoid.powers (f g)).comap f := by
    rintro x ⟨n, rfl⟩
    exact ⟨n, by simp [map_pow]⟩
  refine ⟨⟨IsLocalization.map (Localization.Away (f g)) f hle, IsLocalization.map_comp hle⟩, fun x' => ?_⟩
  simp [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
