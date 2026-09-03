import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero

theorem AlgebraicCurve.Divisor.exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (t : F) (hsepK : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (D : AlgebraicCurve.Divisor K F) (f : F) (hf : f ≠ 0)
    (hD : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) * D v = v.ord f)
    (h0 : f⁻¹ • KaehlerDifferential.D K F f = 0) :
    ∃ g : F, g ≠ 0 ∧ f = g ^ p ∧ ∀ v : AlgebraicCurve.Place K F, D v = v.ord g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero.solution
