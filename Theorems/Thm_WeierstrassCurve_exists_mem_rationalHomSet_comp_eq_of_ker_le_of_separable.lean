import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable

open Polynomial

theorem WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable
    {F : Type*} [Field F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k]
    (W₁ W₂ W₃ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
    {φ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₃)
    {P S N₀ N₁ R : F[X]} (hP : P.Monic) (hdeg : P.natDegree = S.natDegree + 1)
    (hcop : IsCoprime P S) {B : Set k} (hB : B.Finite)
    (hφ : ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
      aeval x S ≠ 0 ∧ aeval x R ≠ 0 ∧
      ∃ h', φ (.some x y h) =
        .some (aeval x P / aeval x S) ((aeval x N₀ + aeval x N₁ * y) / aeval x R) h')
    (hker : ∀ T, φ T = 0 → α T = 0) :
    ∃ β ∈ WeierstrassCurve.rationalHomSet k W₂ W₃, ∀ T, α T = β (φ T) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable.solution
