import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import P2M.Util
namespace P2MW.S_ModularCurve_ModularPolynomialData_exists_veluQuotient2_j_eq_of_mem_roots_fibrePoly
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluX_empty

set_option autoImplicit false

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine

theorem AtwoRootAux.twoTorsionPair {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (W : WeierstrassCurve K)
    {x₀ : K} (hx : 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ = 0) :
    W.toAffine.Equation x₀ (-(W.a₁ * x₀ + W.a₃) / 2) ∧ W.veluGy x₀ (-(W.a₁ * x₀ + W.a₃) / 2) = 0 := by
  constructor
  · rw [Affine.equation_iff]
    simp only [b₂, b₄, b₆] at hx
    field_simp
    linear_combination -hx
  · simp only [veluGy]
    field_simp
    ring

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (data : ModularPolynomialData 2) (W : WeierstrassCurve K) [W.IsElliptic]
    {y : K} (hy : y ∈ (fibrePoly data.Φ W.j).roots) :
    ∃ x₀ y₀ : K, W.toAffine.Equation x₀ y₀ ∧ W.veluGy x₀ y₀ = 0 ∧
      ∃ hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0,
        @WeierstrassCurve.j K _ (W.veluQuotient2 x₀ y₀) ⟨isUnit_iff_ne_zero.mpr hΔ⟩ = y := by

  set P : Cubic K := W.twoTorsionPolynomial with hP
  have ha : P.a ≠ 0 := by
    show (4 : K) ≠ 0
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hsplit : (Polynomial.map (RingHom.id K) P.toPoly).Splits := IsAlgClosed.splits _
  obtain ⟨x₁, x₂, x₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplit
  have hdisc : P.discr ≠ 0 :=
    W.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) W.isUnit_Δ
  have hnodup : (Cubic.map (RingHom.id K) P).roots.Nodup :=
    (Cubic.discr_ne_zero_iff_roots_nodup ha hsplit).mp hdisc
  rw [h3] at hnodup
  have h12 : x₁ ≠ x₂ := by intro h; subst h; simp at hnodup
  have h13 : x₁ ≠ x₃ := by intro h; subst h; simp at hnodup
  have h23 : x₂ ≠ x₃ := by intro h; subst h; simp at hnodup

  have ha' : (Cubic.map (RingHom.id K) P).a ≠ 0 := by simpa [Cubic.map] using ha
  have hroot : ∀ x ∈ ({x₁, x₂, x₃} : Multiset K),
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
    intro x hx
    have hx' : x ∈ (Cubic.map (RingHom.id K) P).roots := by rw [h3]; exact hx
    have := (Cubic.mem_roots_iff (Cubic.ne_zero_of_a_ne_zero ha') x).mp hx'
    simpa [Cubic.map, hP, twoTorsionPolynomial] using this

  let yy : K → K := fun x => -(W.a₁ * x + W.a₃) / 2
  let Q : Fin 3 → K × K := ![(x₁, yy x₁), (x₂, yy x₂), (x₃, yy x₃)]
  have hQfst : ∀ i, (Q i).1 ∈ ({x₁, x₂, x₃} : Multiset K) := by
    intro i; fin_cases i <;> simp [Q]
  have hQsnd : ∀ i, (Q i).2 = yy (Q i).1 := by
    intro i; fin_cases i <;> rfl
  have hQpair : ∀ i, W.toAffine.Equation (Q i).1 (Q i).2 ∧ W.veluGy (Q i).1 (Q i).2 = 0 := by
    intro i; rw [hQsnd]; exact AtwoRootAux.twoTorsionPair h2 W (hroot _ (hQfst i))
  have hQinj : Function.Injective Q := by
    intro i i' h
    have h1 := congrArg Prod.fst h
    fin_cases i <;> fin_cases i' <;> simp [Q] at h1 ⊢ <;> simp_all
  have hΔ : ∀ i, (W.veluQuotient2 (Q i).1 (Q i).2).Δ ≠ 0 := fun i =>
    (@WeierstrassCurve.isUnit_Δ _ _ (W.veluQuotient2 (Q i).1 (Q i).2)
      (WeierstrassCurve.isElliptic_veluQuotient2_of_isElliptic (hQpair i).1 (hQpair i).2)).ne_zero
  have hprod := ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j h2 data W
    (by simp) Q hQinj (fun i => (hQpair i).1) (fun i => (hQpair i).2) hΔ
  rw [hprod] at hy
  obtain ⟨-, hr⟩ := Polynomial.mem_roots'.mp hy
  rw [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hr
  obtain ⟨i, -, hi⟩ := hr
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hi
  exact ⟨(Q i).1, (Q i).2, (hQpair i).1, (hQpair i).2, hΔ i, hi.symm⟩
