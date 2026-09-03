import Definitions.Def_LanglandsTunnell_C4Character
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_split_place_artinValue4_ne
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.P2

theorem LanglandsTunnell.exists_split_place_artinValue4_ne
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1) :
    ∀ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))), ∃ v ∉ S,
      ∃ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 ↥(fixFld (c4H e))),
      𝔓₁ ≠ 𝔓₂ ∧ 𝔓₁.under (𝓞 ↥(fixFld (quatH e))) = v ∧ 𝔓₂.under (𝓞 ↥(fixFld (quatH e))) = v ∧
      artinValue4 e hζ 𝔓₁ ≠ artinValue4 e hζ 𝔓₂ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_split_place_artinValue4_ne.solution
