import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve ModularCurve.XHDRLevel
open ModularCurve in

theorem ModularCurve.XHDRModelAtP.mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)
    (e : (ZMod M)ˣ)
    (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (f : ↥(ModularCurve.xHFunctionFieldBar M H))
    (hDf : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) :
    (AlgebraicCurve.Pic0.mk (SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (diamondAutHBar M H e)) D) : ModularCurve.JH M H) =
        ModularCurve.genOpH M H S (CohCarrier.Gen.dia e) (AlgebraicCurve.Pic0.mk D) ∧
    ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • ((SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (diamondAutHBar M H e)) D :
          AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) :
            AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v =
        v.ord (diamondAutHBar M H e f) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord.solution
