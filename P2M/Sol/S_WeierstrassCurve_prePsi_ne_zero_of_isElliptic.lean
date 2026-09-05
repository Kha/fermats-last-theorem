module

import P2M.Sol.S_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import P2M.Sol.S_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff
import P2M.Sol.S_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import P2M.Util
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace P2MW.S_WeierstrassCurve_prePsi_ne_zero_of_isElliptic

set_option autoImplicit false

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ a₃ preΨ_ofNat a₁ map Ψ₂Sq a₄ a₂ a₆ Affine.Point.some preΨ_ne_zero map_preΨ' preΨ' toAffine Affine.Point map_Δ Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Affine.equation_iff natDegree_Ψ₂Sq Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi Affine.Point.two_smul_some_eq_zero_iff Psi2Sq_ne_zero_of_isElliptic"
p2m_open "WeierstrassCurve"

theorem exists_nonsingular_of_isAlgClosed' {K : Type*} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] (h2 : (2 : K) ≠ 0) (x : K) :
    ∃ y, W.toAffine.Nonsingular x y := by
  set b := W.a₁ * x + W.a₃ with hb
  set c := x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ with hc
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (b ^ 2 + 4 * c)
  refine ⟨(s - b) / 2, (Affine.equation_iff_nonsingular).mp ?_⟩
  rw [Affine.equation_iff]
  field_simp
  linear_combination (-1 : K) * hs

theorem prePsi_ne_zero_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : Odd n) :
    W.preΨ' n ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := hn
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hdeg2 : W.Ψ₂Sq.degree ≠ 0 := by
    rw [degree_eq_natDegree (Psi2Sq_ne_zero_of_isElliptic W), natDegree_Ψ₂Sq W h4]
    exact_mod_cast (by norm_num : (3 : ℕ) ≠ 0)
  obtain ⟨x₂, hx₂⟩ := IsAlgClosed.exists_root _ hdeg2
  obtain ⟨y₂, hns₂⟩ := exists_nonsingular_of_isAlgClosed' W h2 x₂
  have h2t := (Affine.Point.two_smul_some_eq_zero_iff W hns₂).mpr hx₂
  have hnt := (Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W ⟨k, hk⟩ hns₂).mpr (by rw [h0, eval_zero])
  apply Affine.Point.some_ne_zero hns₂
  have e : (2 * k + 1) • Affine.Point.some x₂ y₂ hns₂
      = (k * 2) • Affine.Point.some x₂ y₂ hns₂ + Affine.Point.some x₂ y₂ hns₂ := by
    rw [mul_comm k 2, add_nsmul, one_nsmul]
  rw [← smul_smul, h2t, smul_zero, zero_add, ← hk, hnt] at e
  exact e.symm

theorem prePsi_ne_zero_of_isElliptic' {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : Odd n) : W.preΨ' n ≠ 0 := by
  classical
  by_cases hnK : (n : K) = 0
  ·
    have h2 : (2 : K) ≠ 0 := by
      intro h2
      obtain ⟨p, hp⟩ := CharP.exists K
      have hpn : p ∣ n := (CharP.cast_eq_zero_iff K p n).mp hnK
      have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h2)
      have hp1 : p ≠ 1 := by
        rintro rfl
        exact CharP.ringChar_ne_one (R := K) ((ringChar.eq K 1).symm ▸ rfl)
      have : p = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h | h
        · exact absurd h hp1
        · exact h
      subst this
      exact hn.not_two_dvd_nat hpn

    let K' := AlgebraicClosure K
    haveI : (W.map (algebraMap K K')).IsElliptic := by
      refine ⟨?_⟩
      rw [map_Δ]
      exact W.isUnit_Δ.map _
    have h2' : (2 : K') ≠ 0 := by
      intro h
      apply h2
      exact (algebraMap K K').injective (by rw [map_ofNat, map_zero]; exact h)
    have hne := prePsi_ne_zero_of_isAlgClosed (W.map (algebraMap K K')) h2' hn
    rw [map_preΨ'] at hne
    intro h0
    exact hne (by rw [h0, Polynomial.map_zero])
  · have := W.preΨ_ne_zero (n := (n : ℤ)) (by exact_mod_cast hnK)
    rwa [preΨ_ofNat] at this

end WeierstrassCurve

theorem solution {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : Odd n) : W.preΨ' n ≠ 0 :=
  WeierstrassCurve.prePsi_ne_zero_of_isElliptic' W hn
end S_WeierstrassCurve_prePsi_ne_zero_of_isElliptic
end P2MW

public section
open Polynomial WeierstrassCurve
theorem WeierstrassCurve.prePsi_ne_zero_of_isElliptic {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : Odd n) : W.preΨ' n ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_prePsi_ne_zero_of_isElliptic.solution
end
