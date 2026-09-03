import Mathlib.LinearAlgebra.Determinant
import Mathlib.NumberTheory.Padics.PadicIntegers
import P2M.Util
import P2M.Sol.S_PadicInt_natCard_quotient_range_eq_pow_valuation_det
set_option autoImplicit false

theorem PadicInt.natCard_quotient_range_eq_pow_valuation_det (p : ℕ) [Fact p.Prime]
    {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
    (f : Module.End ℤ_[p] T) (hf : LinearMap.det f ≠ 0) :
    Nat.card (T ⧸ LinearMap.range f) = p ^ (LinearMap.det f).valuation := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_natCard_quotient_range_eq_pow_valuation_det.solution
