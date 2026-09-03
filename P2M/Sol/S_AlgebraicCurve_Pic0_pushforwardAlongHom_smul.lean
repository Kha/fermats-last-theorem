import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Pic0_pushforwardAlongHom_smul

set_option autoImplicit false

noncomputable section

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin)
    (hgg' : IntertwinesAlong φ.toRingHom g g') (x : Pic0 K F') :
    Pic0.pushforwardAlongHom φ hφ hfin hN (g' • x) = g • Pic0.pushforwardAlongHom φ hφ hfin hN x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [pic0_smul_mk, Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk, pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [Pic0.coe_pushforwardAlongDegZero, coe_degZeroSMulHom, coe_degZeroSMulHom,
    Pic0.coe_pushforwardAlongDegZero]
  exact SemilinearAut.pushforwardAlong_smul φ hφ hgg' (D : Divisor K F')
