import Definitions.Def_LanglandsTunnell_C8Character
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_liftTraceSeed_sylowH_table_eq_artinValue
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.liftTraceSeed_sylowH_table_eq_artinValue
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    [Algebra ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e))] [IsScalarTower ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) L]
    {ζ : ℂ} (hζ : ζ ^ 4 = -1) (hpin : ζ + ζ ^ 3 = iotaZsqrtdNegTwo Zsqrtd.sqrtd) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (sylowH e)))), ∀ v ∉ S,
      (∀ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 ↥(fixFld (P2.c8H e))), 𝔓₁ ≠ 𝔓₂ →
          𝔓₁.under (𝓞 ↥(fixFld (sylowH e))) = v → 𝔓₂.under (𝓞 ↥(fixFld (sylowH e))) = v →
        iotaZsqrtdNegTwo ((P2.liftTraceSeed e (sylowH e)).a v) =
            (P2.artinValue e hζ 𝔓₁ : ℂ) + P2.artinValue e hζ 𝔓₂ ∧
          iotaZsqrtdNegTwo ((P2.liftTraceSeed e (sylowH e)).b v) =
            (P2.artinValue e hζ 𝔓₁ : ℂ) * P2.artinValue e hζ 𝔓₂) ∧
      (∀ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (P2.c8H e))), 𝔓.under (𝓞 ↥(fixFld (sylowH e))) = v →
          v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2 →
        (P2.liftTraceSeed e (sylowH e)).a v = 0 ∧
          iotaZsqrtdNegTwo ((P2.liftTraceSeed e (sylowH e)).b v) = -(P2.artinValue e hζ 𝔓 : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_liftTraceSeed_sylowH_table_eq_artinValue.solution
