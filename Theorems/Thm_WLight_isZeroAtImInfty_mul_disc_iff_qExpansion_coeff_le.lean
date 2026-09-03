import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Basic
import P2M.Util
import P2M.Sol.S_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le (N : ℕ) [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hM : 1 ≤ M) (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) N)
    (hFbd : IsBoundedAtImInfty (F * ModularForm.discriminant ^ M)) :
    IsZeroAtImInfty (F * ModularForm.discriminant) ↔
      ∀ n ≤ N * (M - 1),
        (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ M)).coeff n = 0 := by p2m_exact_reverting @_root_.P2MW.S_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le.solution
