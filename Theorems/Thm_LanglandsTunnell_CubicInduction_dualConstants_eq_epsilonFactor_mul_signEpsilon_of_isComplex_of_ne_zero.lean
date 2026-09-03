import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ArchEpsilon
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isComplex_of_ne_zero

set_option autoImplicit false

open NumberField LanglandsTunnell.CubicLambda
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isComplex_of_ne_zero
    (K : Type) [Field K] [NumberField K]
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (wC : InfinitePlace K) (hC : wC.IsComplex) (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (hplaces : ∀ w : InfinitePlace K, w = wC ∨ w = w₀)
    (hk : kC wC hC ≠ 0) (t : ℂ) (e : ℤ) :
    ((RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)).twist t
          (e : ZMod 2)).epsilonFactor *
        signEpsilon (aR w₀ h₀ + (e : ZMod 2)) =
      ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
          fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
        ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
            fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
        ∏ w : InfinitePlace K, lambdaArch K w := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isComplex_of_ne_zero.solution
