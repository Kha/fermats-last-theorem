import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd

set_option autoImplicit false
open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative

theorem LanglandsTunnell.P2.Artin.eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (𝔣 𝔣' : Ideal (𝓞 E)) (h𝔣' : 𝔣' ≠ ⊥) (hdvd : 𝔣 ∣ 𝔣')
    (hsupp : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔣' → v.asIdeal ∣ 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hprinc : M4aHerbrand.principalIdeles (𝓞 E) E ≤ r.ker) (hunits : unitIdeles E 𝔣 ≤ r.ker)
    (hiv' : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣' u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)
    (u : (AdeleRing (𝓞 E) E)ˣ) (hu : IsAdjuster E 𝔣 u 1) :
    r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd.solution
