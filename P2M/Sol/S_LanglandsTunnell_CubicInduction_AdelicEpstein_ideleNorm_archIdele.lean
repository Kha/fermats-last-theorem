import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import P2M.Util
namespace P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_ideleNorm_archIdele
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicVolume LanglandsTunnell.CubicInduction.AdelicEpstein

namespace ArchNormLift

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

private theorem mult_ratInfinitePlace : Rat.infinitePlace.mult = 1 :=
  InfinitePlace.mult_isReal ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩

private theorem prod_infinitePlace_rat (f : InfinitePlace ℚ → ℝ) : ∏ w : InfinitePlace ℚ, f w = f Rat.infinitePlace :=
  Fintype.prod_unique f

private theorem ideleNorm_eq_norm_fst_of_snd_eq_one (a : 𝔸ˣ) (ha : (a : 𝔸).2 = 1) :
    TateGlobal.ideleNorm ℚ a = ‖(a : 𝔸).1 Rat.infinitePlace‖ := by
  rw [TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one ℚ a ha, prod_infinitePlace_rat,
    mult_ratInfinitePlace, pow_one]

private theorem ofReal_ne_zero {t : ℝ} (ht : t ≠ 0) : ofReal t ≠ 0 := by
  unfold ofReal
  simpa using ht

private theorem norm_ofReal (t : ℝ) : ‖ofReal t‖ = |t| := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).dist_eq
    (ofReal t) 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h
  have h' : InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (ofReal t) = t :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply t
  rw [h', Real.norm_eq_abs] at h
  exact h.symm

private theorem archIdele_of_ne_zero {t : ℝ} (ht : t ≠ 0) :
    archIdele t = TateGlobal.archUnitHom Rat.infinitePlace (Units.mk0 (ofReal t) (ofReal_ne_zero ht)) := by
  unfold archIdele
  rw [dif_neg ht]

private theorem archIdele_snd (t : ℝ) : ((archIdele t : 𝔸ˣ) : 𝔸).2 = 1 := by
  unfold archIdele
  split_ifs
  · rfl
  · exact archCentralUnit_snd _ _

end ArchNormLift

open LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.AdelicEpstein

theorem solution (s : ℝ) (hs : 0 < s) :
    NumberField.TateGlobal.ideleNorm ℚ (archIdele s) = s := by
  rw [ArchNormLift.ideleNorm_eq_norm_fst_of_snd_eq_one _ (ArchNormLift.archIdele_snd s),
    ArchNormLift.archIdele_of_ne_zero hs.ne', NumberField.TateGlobal.archUnitHom_apply,
    NumberField.AdelicVolume.archCentralUnit_fst_self, Units.val_mk0, ArchNormLift.norm_ofReal, abs_of_pos hs]
