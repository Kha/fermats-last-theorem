import Mathlib
import P2M.Util
namespace P2MW.S_Module_End_exists_dual_ne_zero_forall_apply_eq_mul_of_commute

set_option autoImplicit false

namespace WsF
namespace CommonEigen

open Module

variable {K : Type*} [Field K] [IsAlgClosed K]
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_forall_apply_eq_smul_of_commute [Nontrivial W]
    {ι : Type*} (T : ι → Module.End K W) (hT : ∀ i j, Commute (T i) (T j)) :
    ∃ v : W, v ≠ 0 ∧ ∃ c : ι → K, ∀ i, T i v = c i • v := by
  classical

  let P : ℕ → Prop := fun n => ∃ U : Submodule K W, U ≠ ⊥ ∧ (∀ i, ∀ u ∈ U, T i u ∈ U) ∧ finrank K U = n
  have hP : ∃ n, P n := ⟨finrank K (⊤ : Submodule K W), ⊤, top_ne_bot, fun _ _ _ => trivial, rfl⟩
  obtain ⟨U, hU0, hUinv, hUdim⟩ := Nat.find_spec hP
  have hmin : ∀ U' : Submodule K W, U' ≠ ⊥ → (∀ i, ∀ u ∈ U', T i u ∈ U') → Nat.find hP ≤ finrank K U' :=
    fun U' h0 hinv => Nat.find_min' hP ⟨U', h0, hinv, rfl⟩
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU0

  have hscalar : ∀ i, ∃ c : K, ∀ u ∈ U, T i u = c • u := by
    intro i
    let Ti : Module.End K U := (T i).restrict (hUinv i)
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue Ti
    refine ⟨c, ?_⟩

    let E : Submodule K W := (Ti.eigenspace c).map U.subtype
    have hEle : E ≤ U := by
      rintro _ ⟨u, -, rfl⟩; exact u.2
    have hE0 : E ≠ ⊥ := by
      intro hE
      apply hc
      rw [eq_bot_iff]
      intro u hu
      have : (u : W) ∈ E := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
      rw [hE, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact Subtype.ext this
    have hTi : ∀ u : U, (Ti u : W) = T i (u : W) := fun u => rfl
    have hEinv : ∀ j, ∀ w ∈ E, T j w ∈ E := by
      intro j w hw
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
      refine Submodule.mem_map.mpr ⟨⟨T j u, hUinv j u u.2⟩, ?_, rfl⟩
      have hu' : T i (u : W) = c • (u : W) := by
        have := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hu); rwa [hTi] at this
      refine Module.End.mem_eigenspace_iff.mpr (Subtype.ext ?_)
      show T i (T j u) = c • T j u
      rw [← Module.End.mul_apply, (hT i j).eq, Module.End.mul_apply, hu', map_smul]
    have hEeq : E = U := by
      refine Submodule.eq_of_le_of_finrank_le hEle ?_
      rw [hUdim]; exact hmin E hE0 hEinv
    intro u hu
    have huE : u ∈ E := hEeq ▸ hu
    obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp huE
    have := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hu')
    rwa [hTi] at this
  choose c hc using hscalar
  obtain ⟨v, hvU, hv0⟩ := (Submodule.ne_bot_iff U).mp hU0
  exact ⟨v, hv0, c, fun i => hc i v hvU⟩

theorem exists_dual_ne_zero_forall_comp_eq_smul_of_commute [Nontrivial W]
    {ι : Type*} (T : ι → Module.End K W) (hT : ∀ i j, Commute (T i) (T j)) :
    ∃ (μ : W →ₗ[K] K) (c : ι → K), μ ≠ 0 ∧ ∀ (i : ι) (w : W), μ (T i w) = c i * μ w := by

  let T' : ι → Module.End K (Module.Dual K W) := fun i => (T i).dualMap
  have hT' : ∀ i j, Commute (T' i) (T' j) := by
    intro i j
    show (T i).dualMap ∘ₗ (T j).dualMap = (T j).dualMap ∘ₗ (T i).dualMap
    rw [LinearMap.dualMap_comp_dualMap, LinearMap.dualMap_comp_dualMap]
    exact congrArg LinearMap.dualMap (hT j i).eq
  haveI : Nontrivial (Module.Dual K W) := by
    rw [← Module.finrank_pos_iff (R := K), Subspace.dual_finrank_eq]; exact Module.finrank_pos
  obtain ⟨μ, hμ0, c, hc⟩ := exists_forall_apply_eq_smul_of_commute T' hT'
  refine ⟨μ, c, hμ0, fun i w => ?_⟩
  have := congrArg (fun φ : Module.Dual K W => φ w) (hc i)
  simpa [T', LinearMap.dualMap_apply] using this

end WsF.CommonEigen

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Nontrivial W]
    {ι : Type*} (T : ι → Module.End K W) (hT : ∀ i j : ι, Commute (T i) (T j)) :
    ∃ (μ : W →ₗ[K] K) (c : ι → K), μ ≠ 0 ∧ ∀ (i : ι) (w : W), μ (T i w) = c i * μ w :=
  WsF.CommonEigen.exists_dual_ne_zero_forall_comp_eq_smul_of_commute T hT
