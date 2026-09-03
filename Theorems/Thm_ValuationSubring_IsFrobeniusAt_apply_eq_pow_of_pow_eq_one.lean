import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one

theorem ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q m : ℕ)
    (hA : A.LiesOverPrime q) (hσ : A.IsFrobeniusAt σ q) (hm : m.Coprime q)
    (ζ : L) (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ q := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one.solution
