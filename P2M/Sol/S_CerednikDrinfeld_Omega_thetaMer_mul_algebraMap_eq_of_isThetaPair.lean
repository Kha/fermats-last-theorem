import Definitions.Def_CerednikDrinfeld_ThetaMer
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_thetaMer_mul_algebraMap_eq_of_isThetaPair

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_thetaMer_mul_algebraMap_eq_of_isThetaPair.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "IsThetaPair thetaMer thetaMer_def_of_exists PseudoUniformizer holRing merField pmoebius upperHalfPlane theta"
namespace ThetaMerLaws
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem cross_eq (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    {F H F₁ H₁ : ↥(holRing ϖ)} (h : IsThetaPair ϖ ρ a b z₀ F H) (h₁ : IsThetaPair ϖ ρ a b z₀ F₁ H₁) :
    H * F₁ = H₁ * F := by
  apply Subtype.ext
  funext z
  show (H : ↥(upperHalfPlane K₀ K) → K) z * (F₁ : ↥(upperHalfPlane K₀ K) → K) z =
    (H₁ : ↥(upperHalfPlane K₀ K) → K) z * (F : ↥(upperHalfPlane K₀ K) → K) z
  by_cases hz : ∃ γ : G, pmoebius K₀ (ρ γ) b = (z : K)
  · rw [(h.2.1 z).2 hz, (h₁.2.1 z).2 hz, zero_mul, zero_mul]
  · have hH : (H : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 := fun h0 => hz ((h.2.1 z).1 h0)
    have hH₁ : (H₁ : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 := fun h0 => hz ((h₁.2.1 z).1 h0)
    have hq := (h.2.2.2 z hz).trans (h₁.2.2.2 z hz).symm
    rw [div_eq_div_iff hH hH₁] at hq
    rw [mul_comm ((H : ↥(upperHalfPlane K₀ K) → K) z), ← hq, mul_comm]

theorem main (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (F H : ↥(holRing ϖ)) (h : IsThetaPair ϖ ρ a b z₀ F H) :
    thetaMer ϖ ρ a b z₀ = Localization.mk F ⟨H, h.1⟩ := by
  have h' : ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H := ⟨F, H, h⟩
  rw [thetaMer_def_of_exists ϖ ρ a b z₀ h', Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  exact cross_eq ϖ ρ a b z₀ h h'.choose_spec.choose_spec

theorem algebraMap_eq_mk (ϖ : PseudoUniformizer K₀ K) (x : ↥(holRing ϖ)) :
    algebraMap ↥(holRing ϖ) (merField ϖ) x = Localization.mk x 1 := by
  rw [Localization.mk_eq_mk', IsLocalization.mk'_one]

theorem main3 (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (F H : ↥(holRing ϖ)) (h : IsThetaPair ϖ ρ a b z₀ F H) :
    thetaMer ϖ ρ a b z₀ * algebraMap ↥(holRing ϖ) (merField ϖ) H = algebraMap ↥(holRing ϖ) (merField ϖ) F := by
  rw [main ϖ ρ a b z₀ F H h, algebraMap_eq_mk, algebraMap_eq_mk, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, mul_one]
  exact mul_comm _ _

end CerednikDrinfeld.Omega.ThetaMerLaws

theorem solution
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (F H : ↥(holRing ϖ)) (h : IsThetaPair ϖ ρ a b z₀ F H) :
    thetaMer ϖ ρ a b z₀ * algebraMap ↥(holRing ϖ) (merField ϖ) H = algebraMap ↥(holRing ϖ) (merField ϖ) F :=
  CerednikDrinfeld.Omega.ThetaMerLaws.main3 ϖ ρ a b z₀ F H h
