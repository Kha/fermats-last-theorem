import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ArchEpsilon
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isReal_split

set_option autoImplicit false

open NumberField LanglandsTunnell.CubicLambda
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isReal_split
    (K : Type) [Field K] [NumberField K]
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal) (w₁ : InfinitePlace K) (h₁ : w₁.IsReal)
    (w₂ : InfinitePlace K) (h₂ : w₂.IsReal)
    (h₀₁ : w₀ ≠ w₁) (h₀₂ : w₀ ≠ w₂) (h₁₂ : w₁ ≠ w₂)
    (hplaces : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)
    (t : ℂ) (e : ℤ) :
    ((RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)).twist t (e : ZMod 2)).epsilonFactor *
        signEpsilon (aR w₀ h₀ + (e : ZMod 2)) =
      ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
          fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
        ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
            fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
        ∏ w : InfinitePlace K, lambdaArch K w := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isReal_split.solution
