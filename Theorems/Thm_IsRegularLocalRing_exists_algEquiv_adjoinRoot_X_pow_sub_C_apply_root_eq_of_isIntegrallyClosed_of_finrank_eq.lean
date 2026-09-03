import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq
    {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (hdim : ringKrullDim R ≤ 2)
    {t : R} (ht : t ∈ maximalIdeal R) (ht2 : t ∉ maximalIdeal R ^ 2) {e : ℕ} (he : 0 < e)
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type*) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    (hdeg : Module.finrank K₀ F = e)
    (θ : B) (hθ : θ ^ e = algebraMap R B t) :
    ∃ φ : AdjoinRoot (X ^ e - C t : R[X]) ≃ₐ[R] B, φ (AdjoinRoot.root (X ^ e - C t : R[X])) = θ := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq.solution
