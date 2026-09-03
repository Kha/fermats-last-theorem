import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
namespace P2MW.S_ModularCurve_genDiffModL_dia_inv_smul_D

set_option autoImplicit false

theorem solution
    (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (S : Set ℕ) (e : (ZMod M)ˣ)
    (f : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :
    ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia e)
        (f⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) f) =
      (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            ModularCurve.diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM)
              (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)⁻¹) f)⁻¹ •
        KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
          (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            ModularCurve.diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM)
              (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)⁻¹) f) := by
  rw [ModularCurve.genDiffModL_dia, ModularCurve.diamondDiffModLH_apply,
    AlgebraicCurve.Differential.pullbackAlong_smul, AlgebraicCurve.Differential.pullbackAlong_D,
    map_inv₀]
  rfl
