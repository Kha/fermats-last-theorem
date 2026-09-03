import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_GluedPic0_eq_zero_of_mem_range_nodeUnit_of_pow_char_smul_eq_zero

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.GluedPic0.eq_zero_of_mem_range_nodeUnit_of_pow_char_smul_eq_zero
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hCB : ConstantsAreBase K F)
    (S : Finset (Place K F × Place K F)) (n : ℕ)
    (z : GluedPic0 K F S) (hz : z ∈ (GluedPic0.nodeUnit S).range) (hpz : (p ^ n : ℤ) • z = 0) :
    z = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_GluedPic0_eq_zero_of_mem_range_nodeUnit_of_pow_char_smul_eq_zero.solution
