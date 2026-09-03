import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Theorems.Thm_CerednikDrinfeld_Omega_exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_act
import Theorems.Thm_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow
import Theorems.Thm_CerednikDrinfeld_FormalOmega_IsAdicFrame_isExhausted
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_exists_toOmega_eq_of_mem_affinoid_zero_or_lt
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_surjOn

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
    (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) :
    Set.SurjOn (fun x : AdicPoint K π R => x.toOmega C) Set.univ (Omega.upperHalfPlane K C) := by
  classical
  intro z hz
  obtain ⟨g, hg⟩ := CerednikDrinfeld.Omega.exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted K C ϖ
    (CerednikDrinfeld.FormalOmega.IsAdicFrame.isExhausted ϖ hF)
    (fun a ha => CerednikDrinfeld.FormalOmega.IsAdicFrame.exists_v_eq_zpow ϖ hF a ha) hz
  obtain ⟨x₀, hx₀⟩ := CerednikDrinfeld.FormalOmega.AdicPoint.exists_toOmega_eq_of_mem_affinoid_zero_or_lt ϖ hF _ hg
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | _ g =>
    refine ⟨x₀.act g, Set.mem_univ _, ?_⟩
    show (x₀.act g).toOmega C = z
    rw [CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_act ϖ hF g x₀, hx₀, ← Omega.pmoebius_mul K hz,
      mul_inv_cancel, Omega.pmoebius_one]
