import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RROpens_exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

set_option autoImplicit false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (D : Divisor K F)
    (Z : Finset (Place K F)) (hZ : ∀ z ∈ Z, D z = 0) (c : Place K F → K)
    (P₀ : Place K F) (hP₀Z : P₀ ∉ Z) (hP₀D : D P₀ = 0)
    (x : F) (hx : P₀.ord x = 1) (m : ℕ) (c₀ : K)
    (hdeg : 2 * (g : ℤ) + m + Z.card ≤ Divisor.degree D) :
    ∃ f : F, f ∈ riemannRochSpace (D - Finsupp.single P₀ (m : ℤ)) ∧
      P₀.HasValue (f * x ^ (-(m : ℤ))) c₀ ∧ ∀ z ∈ Z, z.HasValue f (c z) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RROpens_exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue.solution
