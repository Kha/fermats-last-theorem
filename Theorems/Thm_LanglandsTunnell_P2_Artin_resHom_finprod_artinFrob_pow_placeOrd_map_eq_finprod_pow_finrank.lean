import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_resHom_finprod_artinFrob_pow_placeOrd_map_eq_finprod_pow_finrank

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative

theorem LanglandsTunnell.P2.Artin.resHom_finprod_artinFrob_pow_placeOrd_map_eq_finprod_pow_finrank
    (E F N L' : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Field N] [NumberField N]
    [Field L'] [NumberField L']
    [Algebra E F] [Algebra E N] [Algebra F N] [Algebra E L'] [Algebra L' N]
    [IsScalarTower E F N] [IsScalarTower E L' N]
    [IsGalois F N] [IsMulCommutative (N ≃ₐ[F] N)] [IsGalois E L'] [IsMulCommutative (L' ≃ₐ[E] L')]
    (u : (AdeleRing (𝓞 E) E)ˣ)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 E), placeOrd E (projFin E u) v ≠ 0 →
      ∀ Q : Ideal (𝓞 L'), Q.IsMaximal → Q.under (𝓞 E) = v.asIdeal → Q.inertia (L' ≃ₐ[E] L') = ⊥) :
    resHom E L' F N (∏ᶠ w : HeightOneSpectrum (𝓞 F),
        artinFrob F N w ^ placeOrd F (projFin F (Units.map (genuineBaseChange E F).β.toMonoidHom u)) w) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E L' v ^ placeOrd E (projFin E u) v) ^ Module.finrank E F := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_resHom_finprod_artinFrob_pow_placeOrd_map_eq_finprod_pow_finrank.solution
