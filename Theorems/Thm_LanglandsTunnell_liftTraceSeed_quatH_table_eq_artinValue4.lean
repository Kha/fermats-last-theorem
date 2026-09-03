import Definitions.Def_LanglandsTunnell_C4Character
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_liftTraceSeed_quatH_table_eq_artinValue4
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.liftTraceSeed_quatH_table_eq_artinValue4
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))), ∀ v ∉ S,
      (∀ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 ↥(fixFld (P2.c4H e))), 𝔓₁ ≠ 𝔓₂ →
          𝔓₁.under (𝓞 ↥(fixFld (quatH e))) = v → 𝔓₂.under (𝓞 ↥(fixFld (quatH e))) = v →
        iotaZsqrtdNegTwo ((P2.liftTraceSeed e (quatH e)).a v) =
            (P2.artinValue4 e hζ 𝔓₁ : ℂ) + P2.artinValue4 e hζ 𝔓₂ ∧
          iotaZsqrtdNegTwo ((P2.liftTraceSeed e (quatH e)).b v) =
            (P2.artinValue4 e hζ 𝔓₁ : ℂ) * P2.artinValue4 e hζ 𝔓₂) ∧
      (∀ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (P2.c4H e))), 𝔓.under (𝓞 ↥(fixFld (quatH e))) = v →
          v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2 →
        (P2.liftTraceSeed e (quatH e)).a v = 0 ∧
          iotaZsqrtdNegTwo ((P2.liftTraceSeed e (quatH e)).b v) = -(P2.artinValue4 e hζ 𝔓 : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_liftTraceSeed_quatH_table_eq_artinValue4.solution
