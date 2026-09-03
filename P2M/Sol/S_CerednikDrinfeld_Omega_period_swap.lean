import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_period_swap

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace SWAP

theorem crossRatio_swap {K : Type*} [Field K] (z z₀ x y : K) : crossRatio z z₀ x y = crossRatio x y z z₀ := by
  unfold crossRatio
  rw [← neg_sub x z, ← neg_sub y z₀, ← neg_sub y z, ← neg_sub x z₀, neg_mul_neg, neg_mul_neg]
  ring_nf

theorem crossRatio_flip {K : Type*} [Field K] (z z₀ x y : K) : crossRatio z z₀ x y = crossRatio z₀ z y x := by
  unfold crossRatio
  ring_nf

end SWAP

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (α β : G) :
    period ρ a z₀ α β = period ρ z₀ a β α := by

  have hmem : ∀ (g : PGL(2, K₀)) {x : K}, x ∈ upperHalfPlane K₀ K → pmoebius K₀ g x ∈ upperHalfPlane K₀ K :=
    fun g x hx => pmoebius_mem_upperHalfPlane K₀ hx g

  have hterm : ∀ γ : G,
      thetaFactor ρ a (pmoebius K₀ (ρ α) a) z₀ (pmoebius K₀ (ρ β) z₀) γ =
        thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) a (pmoebius K₀ (ρ α) a) γ⁻¹ := by
    intro γ
    unfold thetaFactor

    rw [SWAP.crossRatio_swap]

    rw [← crossRatio_pmoebius (ρ γ⁻¹) (hmem _ ha) (hmem _ (hmem _ ha)) (hmem _ hz₀) hz₀]

    rw [← pmoebius_mul K₀ ha, ← pmoebius_mul K₀ (hmem _ ha), ← map_mul, inv_mul_cancel, map_one, pmoebius_one,
      pmoebius_one]

    exact SWAP.crossRatio_flip _ _ _ _
  unfold period theta
  rw [show (fun γ => thetaFactor ρ a (pmoebius K₀ (ρ α) a) z₀ (pmoebius K₀ (ρ β) z₀) γ) =
      fun γ => thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) a (pmoebius K₀ (ρ α) a) ((Equiv.inv G) γ) from funext hterm]
  exact Equiv.tprod_eq (Equiv.inv G) _
