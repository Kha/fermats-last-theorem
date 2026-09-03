import Definitions.Def_LanglandsTunnell_C4Character
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2 LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem LanglandsTunnell.P2.raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)
    (I : Ideal (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))) (hI : I ≠ ⊥)
    (hIunr : ∀ w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L)),
      FractionalIdeal.count (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L) w
          ((I : Ideal (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))) :
            FractionalIdeal
              ((𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))⁰)
              (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L)) ≠ 0 →
      (primeAbove (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L) L w).inertia
        (L ≃ₐ[ℚ] L) = ⊥) :
    raySymbol (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L) (artinValue4 e hζ)
        ((I : Ideal (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))) :
          FractionalIdeal
            ((𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))⁰)
            (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))
      = raySymbol (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L) (artinValue e hζ)
        ((Ideal.relNorm (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) I :
            Ideal (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) :
          FractionalIdeal
            ((𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))⁰)
            (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_raySymbol_artinValue4_eq_raySymbol_artinValue_relNorm_of_inertia_rat.solution
