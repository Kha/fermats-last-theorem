import Mathlib
import Theorems.Thm_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one
import P2M.Util
namespace P2MW.S_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology

theorem solution (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (hneg : -1 ∈ Γ)
    [hdisc : DiscreteTopology ↥Γ] (τ : ℍ) :
    2 ∣ Nat.card ↥(MulAction.stabilizer ↥Γ τ) := by
  obtain ⟨hfin, -⟩ := UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one Γ hdet τ
  haveI := hfin
  have hfixed : ((⟨-1, hneg⟩ : ↥Γ) : ↥Γ) • τ = τ := by
    change (-1 : GL (Fin 2) ℝ) • τ = τ
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos (by simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_neg, Matrix.det_one])]
    simp [num, denom]
  let m : ↥(MulAction.stabilizer ↥Γ τ) := ⟨⟨-1, hneg⟩, hfixed⟩
  have hm1 : m ≠ 1 := by
    intro h
    have h' : ((m : ↥Γ) : GL (Fin 2) ℝ) = 1 := by
      rw [h]; rfl
    have h'' := congrArg (fun g : GL (Fin 2) ℝ => g.val 0 0) h'
    simp [m] at h''
    norm_num at h''
  have hm2 : m ^ 2 = 1 := by
    apply Subtype.ext; apply Subtype.ext
    show ((-1 : GL (Fin 2) ℝ)) ^ 2 = 1
    exact neg_one_sq
  have horder : orderOf m = 2 := orderOf_eq_prime hm2 hm1
  have h := orderOf_dvd_natCard m
  rwa [horder] at h
