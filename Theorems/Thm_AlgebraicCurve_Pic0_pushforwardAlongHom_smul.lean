import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_pushforwardAlongHom_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut

universe u
theorem AlgebraicCurve.Pic0.pushforwardAlongHom_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin)
    (hgg' : IntertwinesAlong φ.toRingHom g g') (x : Pic0 K F') :
    Pic0.pushforwardAlongHom φ hφ hfin hN (g' • x) = g • Pic0.pushforwardAlongHom φ hφ hfin hN x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_pushforwardAlongHom_smul.solution
