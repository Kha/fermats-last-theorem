import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_exists_smul_eq_and_isPrincipal_sub_of_frobeniusSemilinear

set_option autoImplicit false

theorem AlgebraicCurve.Divisor.exists_smul_eq_and_isPrincipal_sub_of_frobeniusSemilinear
    (K F : Type*) [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] (hKF : AlgebraicCurve.ConstantsAreBase K F)
    (q : ℕ) (β : AlgebraicCurve.SemilinearAut K F)
    (hβK : ∀ a : K, AlgebraicCurve.SemilinearAut.baseAut β a = a ^ q)
    (hβF : ∀ x : F, ∃ n : ℕ, 0 < n ∧ β ^ n • x = x)
    (D : AlgebraicCurve.Divisor K F) (hD : (β • D - D).IsPrincipal) :
    ∃ D' : AlgebraicCurve.Divisor K F, β • D' = D' ∧ (D - D').IsPrincipal := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_exists_smul_eq_and_isPrincipal_sub_of_frobeniusSemilinear.solution
