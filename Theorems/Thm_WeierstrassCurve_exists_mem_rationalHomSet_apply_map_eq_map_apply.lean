import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply {F : Type*} [Field F] (k₀ : Type*) (k : Type*) [Field k₀] [Field k] [Algebra F k₀] [Algebra F k] [Algebra k₀ k] [IsScalarTower F k₀ k] [IsAlgClosed k₀] [DecidableEq k₀] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {α₀ : (W₁⁄k₀).Point →+ (W₂⁄k₀).Point} (hα₀ : α₀ ∈ WeierstrassCurve.rationalHomSet k₀ W₁ W₂) : ∃ α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂, ∀ P : (W₁⁄k₀).Point, α (WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom F k₀ k) P) = WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom F k₀ k) (α₀ P) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply.solution
