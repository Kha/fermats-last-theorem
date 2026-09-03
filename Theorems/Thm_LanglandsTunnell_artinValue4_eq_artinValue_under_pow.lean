import Definitions.Def_LanglandsTunnell_C4Character
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_artinValue4_eq_artinValue_under_pow
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.P2 LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.artinValue4_eq_artinValue_under_pow
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)
    (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L)))
    (hw : (primeAbove (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L) L w).inertia
      (L ≃ₐ[ℚ] L) = ⊥) :
    artinValue4 e hζ w
      = artinValue e hζ (w.under
          (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) ^
        ((w.under (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))).asIdeal.inertiaDeg'
          w.asIdeal) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_artinValue4_eq_artinValue_under_pow.solution
