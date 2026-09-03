import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
namespace P2MW.S_ModularCurve_FullLevel_laurentBaseChange_gamma0_le_fieldBar

set_option autoImplicit false

open scoped MatrixGroups

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup

namespace K1KidsP1

private theorem Gamma0_le_of_dvd {N N' : ℕ} (h : N' ∣ N) : Gamma0 N ≤ Gamma0 N' := by
  intro γ hγ
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
  exact (Int.natCast_dvd_natCast.2 h).trans hγ

private theorem laurentBaseChange_mono (L : Type*) [Field L] [Algebra ℚ L] {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ :=
  IntermediateField.adjoin.mono L _ _ (Set.image_mono fun _ hx => h hx)

end K1KidsP1

theorem solution (q M' : ℕ) :
    ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) ≤
      ModularCurve.FullLevel.fieldBar q M' := by
  exact K1KidsP1.laurentBaseChange_mono _ (qExpFunctionFieldC_mono ℚ
    ((CohCarrier.GammaH_le_Gamma0 (levelH q M')).trans (K1KidsP1.Gamma0_le_of_dvd (dvd_mul_left M' (q ^ 2)))))
