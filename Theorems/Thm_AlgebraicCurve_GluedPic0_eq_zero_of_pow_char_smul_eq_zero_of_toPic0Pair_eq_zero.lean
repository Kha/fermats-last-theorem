import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_GluedPic0_eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.GluedPic0.eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (hCB : ConstantsAreBase K F)
    (S : Finset (Place K F × Place K F))
    (hrat : ∀ s : ↥S,
      Function.Surjective (algebraMap K ((s : Place K F × Place K F).1.ResidueField)) ∧
        Function.Surjective (algebraMap K ((s : Place K F × Place K F).2.ResidueField)))
    (p : ℕ) [Fact p.Prime] [CharP K p] (k : ℕ)
    (x : GluedPic0 K F S) (hx : (p ^ k : ℤ) • x = 0) (h0 : GluedPic0.toPic0Pair S x = 0) :
    x = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_GluedPic0_eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero.solution
