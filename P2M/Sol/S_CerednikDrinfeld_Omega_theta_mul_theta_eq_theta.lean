import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_theta_mul_theta_eq_theta

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace Law3CocAB
theorem cr_mul_cr_right {K : Type*} [Field K] (z z₀ x y w : K) (hyz : y ≠ z) (hyz₀ : y ≠ z₀) :
    crossRatio z z₀ x y * crossRatio z z₀ y w = crossRatio z z₀ x w := by
  simp only [crossRatio]
  have h1 : z - y ≠ 0 := sub_ne_zero.2 (Ne.symm hyz)
  have h2 : z₀ - y ≠ 0 := sub_ne_zero.2 (Ne.symm hyz₀)
  rw [div_mul_div_comm]
  rw [show (z - x) * (z₀ - y) * ((z - y) * (z₀ - w)) = ((z - x) * (z₀ - w)) * ((z - y) * (z₀ - y)) by ring,
    show (z - y) * (z₀ - x) * ((z - w) * (z₀ - y)) = ((z - w) * (z₀ - x)) * ((z - y) * (z₀ - y)) by ring]
  rw [mul_div_mul_right _ _ (mul_ne_zero h1 h2)]
end Law3CocAB

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b c z₀ z : K}
    (hzb : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hab : ThetaMultipliable ρ a b z₀ z) (hbc : ThetaMultipliable ρ b c z₀ z) :
    theta ρ a b z₀ z * theta ρ b c z₀ z = theta ρ a c z₀ z := by
  simp only [theta]
  rw [← Multipliable.tprod_mul hab hbc]
  congr 1
  funext γ
  exact Law3CocAB.cr_mul_cr_right _ _ _ _ _ (hzb γ) (hz₀b γ)
