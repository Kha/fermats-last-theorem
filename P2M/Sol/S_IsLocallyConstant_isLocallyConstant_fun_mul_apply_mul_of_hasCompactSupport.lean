import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Theorems.Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
import P2M.Util
namespace P2MW.S_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport

open Filter Topology

namespace M4aP3B
namespace Rows
namespace SliceLocConst

theorem isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport_impl
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) {S : Type*} (n : S → G) :
    IsLocallyConstant (fun kk : G × G => fun s => f (kk.1 * n s * kk.2)) := by
  obtain ⟨V, hV1, hV⟩ := hf.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport hsupp
  refine (IsLocallyConstant.iff_eventually_eq _).2 ?_
  rintro ⟨k₀, k₀'⟩
  have c1 : Continuous (fun kk : G × G => kk.1 * k₀⁻¹) := continuous_fst.mul continuous_const
  have c2 : Continuous (fun kk : G × G => k₀'⁻¹ * kk.2) := continuous_const.mul continuous_snd
  have t1 : Tendsto (fun kk : G × G => kk.1 * k₀⁻¹) (𝓝 (k₀, k₀')) (𝓝 1) := by
    simpa using c1.tendsto (k₀, k₀')
  have t2 : Tendsto (fun kk : G × G => k₀'⁻¹ * kk.2) (𝓝 (k₀, k₀')) (𝓝 1) := by
    simpa using c2.tendsto (k₀, k₀')
  filter_upwards [t1 hV1, t2 hV1] with kk h1 h2
  funext s
  have e : kk.1 * n s * kk.2 = kk.1 * k₀⁻¹ * (k₀ * n s * k₀') * (k₀'⁻¹ * kk.2) := by
    simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  rw [e]
  exact hV _ h1 _ h2 _

theorem gate_discrete {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    {Y S : Type*} (f : G → Y) (n : S → G) :
    IsLocallyConstant (fun kk : G × G => fun s => f (kk.1 * n s * kk.2)) :=
  IsLocallyConstant.of_discrete _

theorem finite_image_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) {S : Type*} (n : S → G)
    {K : Set (G × G)} (hK : IsCompact K) :
    ((fun kk : G × G => fun s => f (kk.1 * n s * kk.2)) '' K).Finite := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have h := (isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport_impl hf hsupp n).comp_continuous
    continuous_subtype_val (X := K)
  have h__af := h.range_finite
  simp [Set.image_eq_range] at h__af ⊢
  exact h__af

end M4aP3B.Rows.SliceLocConst


theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) {S : Type*} (n : S → G) :
    IsLocallyConstant (fun kk : G × G => fun s => f (kk.1 * n s * kk.2)) := by
  first
    | exact M4aP3B.Rows.SliceLocConst.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport_impl hf hsupp n
    | (apply M4aP3B.Rows.SliceLocConst.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport_impl <;> assumption)
