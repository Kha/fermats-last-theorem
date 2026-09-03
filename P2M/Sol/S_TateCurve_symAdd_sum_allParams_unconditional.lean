import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab
import Theorems.Thm_TateCurve_ks17_D2_exports
import Theorems.Thm_TateCurve_symAdd_sum_regional
import Theorems.Thm_TateCurve_diffHyp_unconditional
import P2M.Util
namespace P2MW.S_TateCurve_symAdd_sum_allParams_unconditional
attribute [-simp] WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero

open scoped NNReal
p2m_open "TateCurve P2MW.S_TateCurve_symAdd_sum_allParams_unconditional.TateCurve"

universe u_1 u_2
namespace TateCurve
p2m_export "TateCurve" "symSumNum AddParams pointX pointY DiffHyp ExpansionRegion ks17_D2_exports symAdd_sum_regional diffHyp_unconditional"
p2m_open "TateCurve"

theorem diffHyp_of_region_closed : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] {q τ : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v'))),
      DiffHyp q :=
  TateCurve.ks17_D2_exports.{u_1}.1

theorem exists_sqrt_of_isAlgClosed : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] [IsAlgClosed K] (q : K),
      ∃ τ : K, τ ^ 2 = q :=
  TateCurve.ks17_D2_exports.{u_1}.2.1

theorem symAdd_sum_of_region_closed : ∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] {q u v τ : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hτ : τ ^ 2 = q)
    (hregS1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') + pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        symSumNum q (pointX q u') (pointX q v'))
    (hregD1 : ∀ u' v' : K, ExpansionRegion q u' v' →
      (pointX q (u' * v') - pointX q (u' * v'⁻¹)) * (pointX q u' - pointX q v') ^ 2 =
        -((2 * pointY q u' + pointX q u') * (2 * pointY q v' + pointX q v')))
    (hp : AddParams q u v),
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = symSumNum q (pointX q u) (pointX q v) :=
  TateCurve.ks17_D2_exports.{u_1}.2.2

end TateCurve

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    ∀ u v : K, TateCurve.AddParams q u v →
      (TateCurve.pointX q (u * v) + TateCurve.pointX q (u * v⁻¹)) * (TateCurve.pointX q u - TateCurve.pointX q v) ^ 2 =
        TateCurve.symSumNum q (TateCurve.pointX q u) (TateCurve.pointX q v) := by
  intro u v hp
  obtain ⟨τ, hτ⟩ := TateCurve.exists_sqrt_of_isAlgClosed (K := K) q
  exact TateCurve.symAdd_sum_of_region_closed hq0 hq hτ (TateCurve.symAdd_sum_regional hq0 hq)
    (fun u' v' hreg => TateCurve.diffHyp_unconditional hq0 hq u' v' hreg.params) hp
