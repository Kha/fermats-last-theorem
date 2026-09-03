import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_baseChange_of_isIntegrallyClosed
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open IsLocalRing Polynomial

open scoped TensorProduct

theorem IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_baseChange_of_isIntegrallyClosed
    {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (hdim : ringKrullDim R ≤ 2)
    (s : R) (hs : s ∈ maximalIdeal R) (hs2 : s ∉ maximalIdeal R ^ 2)
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R))
    (R' : Type*) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [Module.Finite R R'] [Module.Free R R'] [Algebra.Etale R R']
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type*) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    (hdeg : Module.finrank K₀ F = e)
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B)
    (u' : R'ˣ)
    (e' : R' ⊗[R] B ≃ₐ[R'] AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) :
    ∃ u : Rˣ, Nonempty (B ≃ₐ[R] AdjoinRoot (X ^ e - C ((u : R) * s) : R[X])) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_baseChange_of_isIntegrallyClosed.solution
