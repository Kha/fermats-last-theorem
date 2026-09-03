import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_eq_theta_of_mulEquiv_of_apply_eq_conj

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G₁ G₂ : Type*} [Group G₁] [Group G₂] (ρ₁ : G₁ →* PGL(2, K₀)) (ρ₂ : G₂ →* PGL(2, K₀))
    (e : G₁ ≃* G₂) (n : PGL(2, K₀)) (he : ∀ g : G₁, ρ₂ (e g) = n * ρ₁ g * n⁻¹)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (w : K) (hw : w ∈ upperHalfPlane K₀ K) :
    theta ρ₂ (pmoebius K₀ n a) (pmoebius K₀ n b) (pmoebius K₀ n z₀) (pmoebius K₀ n w) = theta ρ₁ a b z₀ w := by
  have hact : ∀ (g : G₁) {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ₂ (e g)) (pmoebius K₀ n x) = pmoebius K₀ n (pmoebius K₀ (ρ₁ g) x) := by
    intro g x hx
    rw [he, ← pmoebius_mul K₀ hx, mul_assoc, inv_mul_cancel, mul_one, pmoebius_mul K₀ hx]
  simp only [theta]
  rw [← Equiv.tprod_eq e.toEquiv]
  congr 1
  funext δ
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, thetaFactor]
  change crossRatio _ _ (pmoebius K₀ (ρ₂ (e δ)) _) (pmoebius K₀ (ρ₂ (e δ)) _) = _
  have hδa : pmoebius K₀ (ρ₁ δ) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha _
  have hδb : pmoebius K₀ (ρ₁ δ) b ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hb _
  rw [hact δ ha, hact δ hb]
  exact crossRatio_pmoebius n hw hz₀ hδa hδb
