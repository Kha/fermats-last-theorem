import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_exists_pullbackAlong_single_one_eq_sum

set_option autoImplicit false

theorem AlgebraicCurve.Divisor.exists_pullbackAlong_single_one_eq_sum
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFI : AlgebraicCurve.FundamentalIdentityAlong K φ hφ)
    (P : AlgebraicCurve.Place K F) (hdegP : P.deg = 1)
    (hdeg1 : ∀ w : AlgebraicCurve.Place K F', w.restrictAlong φ hφ = P → w.deg = 1)
    (n : ℕ) (hn : AlgebraicCurve.finrankAlong K φ = n) :
    ∃ W : Fin n → AlgebraicCurve.Place K F',
      AlgebraicCurve.Divisor.pullbackAlong φ hφ (Finsupp.single P 1) = ∑ i, Finsupp.single (W i) 1 ∧
        ∀ i, (W i).restrictAlong φ hφ = P := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_exists_pullbackAlong_single_one_eq_sum.solution
