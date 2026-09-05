module

public import Mathlib
public import Definitions.Def_ModularCurve_NodeDescent
public import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import P2M.Sol.S_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import P2M.Sol.S_ModularCurve_NodeLocalized_eval2_branch_eq_zero_of_modularEval_eq_zero
import P2M.Util

namespace P2MW.S_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint.ModularCurve.NodeLocalized"
open MvPolynomial

namespace ModularCurve
p2m_export "ModularCurve" "NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero NodeLocalized.eval2_branch_eq_zero_of_modularEval_eq_zero"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring redRestrict modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint modularEvalAt evalRange nodeDenominators pointEval_eq_zero_of_modularEval_eq_zero eval2_branch_eq_zero_of_modularEval_eq_zero"
p2m_open "ModularCurve.NodeLocalized"
namespace Branch

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ))

local notation "Ψ₀" => MvPolynomial.eval₂Hom (Polynomial.C.comp (redRestrict red K))
  ![(Polynomial.X : Polynomial k), Polynomial.X ^ q]
local notation "Ψ₁" => MvPolynomial.eval₂Hom (Polynomial.C.comp (redRestrict red K))
  ![(Polynomial.X : Polynomial k) ^ q, Polynomial.X]

section Taylor
variable (B : Type*) [CommRing B]

noncomputable abbrev ι₀ : Polynomial B →+* MvPolynomial (Fin 2) B := Polynomial.eval₂RingHom C (X 0)

noncomputable abbrev ι₁ : Polynomial B →+* MvPolynomial (Fin 2) B := Polynomial.eval₂RingHom C (X 1)

noncomputable abbrev σ₀ (q : ℕ) : MvPolynomial (Fin 2) B →+* Polynomial B := eval₂Hom Polynomial.C ![Polynomial.X, Polynomial.X ^ q]

noncomputable abbrev σ₁ (q : ℕ) : MvPolynomial (Fin 2) B →+* Polynomial B := eval₂Hom Polynomial.C ![Polynomial.X ^ q, Polynomial.X]

omit [Fact q.Prime] in
theorem sub_ι₀_σ₀_mem (s : MvPolynomial (Fin 2) B) :
    s - ι₀ B (σ₀ B q s) ∈ Ideal.span {(X 1 : MvPolynomial (Fin 2) B) - X 0 ^ q} := by
  induction s using MvPolynomial.induction_on with
  | C c =>
    rw [coe_eval₂Hom, eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, sub_self]; exact zero_mem _
  | add p r hp hr =>
    have : p + r - ι₀ B (σ₀ B q (p + r)) = (p - ι₀ B (σ₀ B q p)) + (r - ι₀ B (σ₀ B q r)) := by
      rw [map_add, map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p j hp =>
    have key : p * X j - ι₀ B (σ₀ B q (p * X j))
        = (p - ι₀ B (σ₀ B q p)) * X j + ι₀ B (σ₀ B q p) * (X j - ι₀ B (![Polynomial.X, Polynomial.X ^ q] j)) := by
      rw [map_mul, map_mul, coe_eval₂Hom, eval₂_X]; ring
    rw [key]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    fin_cases j <;> simp [Polynomial.coe_eval₂RingHom]

omit [Fact q.Prime] in
theorem sub_ι₁_σ₁_mem (s : MvPolynomial (Fin 2) B) :
    s - ι₁ B (σ₁ B q s) ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) B) - X 1 ^ q} := by
  induction s using MvPolynomial.induction_on with
  | C c =>
    rw [coe_eval₂Hom, eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, sub_self]; exact zero_mem _
  | add p r hp hr =>
    have : p + r - ι₁ B (σ₁ B q (p + r)) = (p - ι₁ B (σ₁ B q p)) + (r - ι₁ B (σ₁ B q r)) := by
      rw [map_add, map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p j hp =>
    have key : p * X j - ι₁ B (σ₁ B q (p * X j))
        = (p - ι₁ B (σ₁ B q p)) * X j + ι₁ B (σ₁ B q p) * (X j - ι₁ B (![Polynomial.X ^ q, Polynomial.X] j)) := by
      rw [map_mul, map_mul, coe_eval₂Hom, eval₂_X]; ring
    rw [key]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    fin_cases j <;> simp [Polynomial.coe_eval₂RingHom]

end Taylor

section Kernels
variable (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)

omit [CharP k q] in
theorem ψ₀_eq : Ψ₀ = (Polynomial.mapRingHom (redRestrict red K)).comp (σ₀ _ q) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
  · simp [Polynomial.coe_mapRingHom]
  · fin_cases j <;> simp [Polynomial.coe_mapRingHom]

omit [CharP k q] in
theorem ψ₁_eq : Ψ₁ = (Polynomial.mapRingHom (redRestrict red K)).comp (σ₁ _ q) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
  · simp [Polynomial.coe_mapRingHom]
  · fin_cases j <;> simp [Polynomial.coe_mapRingHom]

omit [CharP k q] in
include hϖ in

theorem C_dvd_of_map_eq_zero (P : Polynomial ↥(coeffSubring A K)) (hP : P.map (redRestrict red K) = 0) :
    Polynomial.C ϖ ∣ P := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro n
  have hn := congrArg (fun Q => Polynomial.coeff Q n) hP
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hn
  obtain ⟨d, hd⟩ := (hϖ _).mp hn
  exact ⟨d, hd⟩

omit [CharP k q] in
include hϖ in
theorem mem_span₀_iff (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    s ∈ Ideal.span {C ϖ, (X 1 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 0 ^ q} ↔ Ψ₀ s = 0 := by
  constructor
  · intro hs
    have hle : Ideal.span {C ϖ, (X 1 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 0 ^ q} ≤ RingHom.ker Ψ₀ := by
      rw [Ideal.span_le]
      rintro _ (rfl | rfl)
      · rw [SetLike.mem_coe, RingHom.mem_ker, eval₂Hom_C, RingHom.comp_apply, (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩, map_zero]
      · rw [SetLike.mem_coe, RingHom.mem_ker]; simp
    exact (RingHom.mem_ker).mp (hle hs)
  · intro hs
    rw [ψ₀_eq, RingHom.comp_apply, Polynomial.coe_mapRingHom] at hs
    obtain ⟨t, ht⟩ := C_dvd_of_map_eq_zero red K ϖ hϖ _ hs
    have : s = (s - ι₀ _ (σ₀ _ q s)) + ι₀ _ (σ₀ _ q s) := by ring
    rw [this]
    refine add_mem (Ideal.span_mono (Set.subset_insert _ _) (sub_ι₀_σ₀_mem _ s)) ?_
    rw [ht, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

omit [CharP k q] in
include hϖ in
theorem mem_span₁_iff (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    s ∈ Ideal.span {C ϖ, (X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 1 ^ q} ↔ Ψ₁ s = 0 := by
  constructor
  · intro hs
    have hle : Ideal.span {C ϖ, (X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 1 ^ q} ≤ RingHom.ker Ψ₁ := by
      rw [Ideal.span_le]
      rintro _ (rfl | rfl)
      · rw [SetLike.mem_coe, RingHom.mem_ker, eval₂Hom_C, RingHom.comp_apply, (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩, map_zero]
      · rw [SetLike.mem_coe, RingHom.mem_ker]; simp
    exact (RingHom.mem_ker).mp (hle hs)
  · intro hs
    rw [ψ₁_eq, RingHom.comp_apply, Polynomial.coe_mapRingHom] at hs
    obtain ⟨t, ht⟩ := C_dvd_of_map_eq_zero red K ϖ hϖ _ hs
    have : s = (s - ι₁ _ (σ₁ _ q s)) + ι₁ _ (σ₁ _ q s) := by ring
    rw [this]
    refine add_mem (Ideal.span_mono (Set.subset_insert _ _) (sub_ι₁_σ₁_mem _ s)) ?_
    rw [ht, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

theorem eval_ψ₀ (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    (Ψ₀ s).eval a = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s := by
  rw [← Polynomial.coe_evalRingHom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom, pointEval]
  congr 2
  · ext c; simp
  · funext i; fin_cases i <;> simp

theorem eval_ψ₁ (ha2 : a ^ (q ^ 2) = a) (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    (Ψ₁ s).eval (a ^ q) = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s := by
  rw [← Polynomial.coe_evalRingHom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom, pointEval]
  congr 2
  · ext c; simp
  · funext i; fin_cases i
    · simp only [Matrix.cons_val_zero, Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_X,
        Fin.zero_eta]
      rw [← pow_mul, show q * q = q ^ 2 from (sq q).symm, ha2]
    · simp

omit [CharP k q] in
theorem X_sub_X_pow_pow_ne_zero : (Polynomial.X : Polynomial k) - (Polynomial.X ^ q) ^ q ≠ 0 := by
  rw [← pow_mul]
  intro h
  have h1 := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
  rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow] at h1
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  nlinarith

end Kernels

theorem main (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    let E := modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)
    ((Ideal.span {E (C ϖ), E (X 1 - X 0 ^ q)}).IsPrime ∧ E (X 0 - X 1 ^ q) ∉ Ideal.span {E (C ϖ), E (X 1 - X 0 ^ q)} ∧
      ∀ c : ↥(coeffSubring A K), E (X 0 - C c) ∉ Ideal.span {E (C ϖ), E (X 1 - X 0 ^ q)}) ∧
    (a ^ (q ^ 2) = a →
      (Ideal.span {E (C ϖ), E (X 0 - X 1 ^ q)}).IsPrime ∧ E (X 1 - X 0 ^ q) ∉ Ideal.span {E (C ϖ), E (X 0 - X 1 ^ q)}) := by
  classical
  intro E
  haveI hfact : Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K)) ≤
      RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
    ⟨fun s hs => (RingHom.mem_ker).mpr
      (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s ((RingHom.mem_ker).mp hs))⟩
  set φ := modularEval (1 * q) (coeffSubring A K) with hφ
  set pe := pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) with hpe
  set ρ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(evalRange (1 * q) (coeffSubring A K)) := φ.rangeRestrict with hρ
  have hE : ∀ p, E p = algebraMap (↥(evalRange (1 * q) (coeffSubring A K))) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) (ρ p) := fun p => rfl
  have hEmap : ∀ J : Ideal (MvPolynomial (Fin 2) ↥(coeffSubring A K)),
      J.map E = (J.map ρ).map (algebraMap (↥(evalRange (1 * q) (coeffSubring A K))) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) := fun J => by
    rw [Ideal.map_map]; congr 1
  have hkerρ : RingHom.ker ρ = RingHom.ker φ := RingHom.ker_rangeRestrict φ
  have hρsurj : Function.Surjective ρ := RingHom.rangeRestrict_surjective φ
  have hinj : Function.Injective (algebraMap (↥(evalRange (1 * q) (coeffSubring A K))) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) := fun u v huv =>
    Subtype.ext (congrArg (fun w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) => (w : LaurentSeries (AlgebraicClosure ℚ))) huv)

  have prime_of : ∀ J : Ideal (MvPolynomial (Fin 2) ↥(coeffSubring A K)),
      J.IsPrime → RingHom.ker φ ≤ J → J ≤ RingHom.ker pe → (J.map E).IsPrime := by
    intro J hJ hkJ hJn
    rw [hEmap]
    have hP : (J.map ρ).IsPrime := Ideal.map_isPrime_of_surjective hρsurj (by rw [hkerρ]; exact hkJ)
    refine IsLocalization.isPrime_of_isPrime_disjoint (nodeDenominators (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) _ hP ?_
    rw [Set.disjoint_left]
    rintro y ⟨s, hs, rfl⟩ hy
    obtain ⟨s', hs', hss'⟩ := (Ideal.mem_map_iff_of_surjective ρ hρsurj).mp hy
    have hd : s - s' ∈ RingHom.ker φ := by
      rw [← hkerρ, RingHom.mem_ker, map_sub, sub_eq_zero]; exact hss'.symm
    have hsJ : s ∈ J := by simpa using J.add_mem (hkJ hd) hs'
    exact hs ((RingHom.mem_ker).mp (hJn hsJ))

  have not_mem_of : ∀ (J : Ideal (MvPolynomial (Fin 2) ↥(coeffSubring A K))) (ψ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* Polynomial k),
      (∀ s, s ∈ J ↔ ψ s = 0) → RingHom.ker φ ≤ J → (∀ s, ψ s = 0 → pe s = 0) →
      ∀ h₀, ψ h₀ ≠ 0 → E h₀ ∉ J.map E := by
    intro J ψ hJ hkJ hψpe h₀ hh₀ hmem
    rw [hEmap, hE] at hmem
    obtain ⟨⟨⟨y, hy⟩, ⟨m, hm⟩⟩, hrel⟩ := (IsLocalization.mem_map_algebraMap_iff (nodeDenominators (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))).mp hmem
    obtain ⟨s, hs, rfl⟩ := hm
    obtain ⟨s', hs', rfl⟩ := (Ideal.mem_map_iff_of_surjective ρ hρsurj).mp hy
    have hρeq : ρ (h₀ * s) = ρ s' := hinj (by rw [map_mul, map_mul]; exact hrel)
    have hdiff : h₀ * s - s' ∈ RingHom.ker φ := by
      rw [← hkerρ, RingHom.mem_ker, map_sub, hρeq, sub_self]
    have hJs : h₀ * s ∈ J := by simpa using J.add_mem (hkJ hdiff) hs'
    have h1 : ψ h₀ * ψ s = 0 := by rw [← map_mul]; exact (hJ _).mp hJs
    rcases mul_eq_zero.mp h1 with h | h
    · exact hh₀ h
    · exact hs (hψpe s h)

  have hk0 : RingHom.ker φ ≤ Ideal.span {C ϖ, (X 1 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 0 ^ q} :=
    fun s hs => (mem_span₀_iff red K ϖ hϖ s).mpr
      (ModularCurve.NodeLocalized.eval2_branch_eq_zero_of_modularEval_eq_zero red K s ((RingHom.mem_ker).mp hs)).1
  have hk1 : RingHom.ker φ ≤ Ideal.span {C ϖ, (X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 1 ^ q} :=
    fun s hs => (mem_span₁_iff red K ϖ hϖ s).mpr
      (ModularCurve.NodeLocalized.eval2_branch_eq_zero_of_modularEval_eq_zero red K s ((RingHom.mem_ker).mp hs)).2
  have hmap0 : (Ideal.span {C ϖ, (X 1 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 0 ^ q}).map E
      = Ideal.span {E (C ϖ), E (X 1 - X 0 ^ q)} := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  have hmap1 : (Ideal.span {C ϖ, (X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 1 ^ q}).map E
      = Ideal.span {E (C ϖ), E (X 0 - X 1 ^ q)} := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  refine ⟨⟨?_, ?_, fun c => ?_⟩, fun ha2 => ⟨?_, ?_⟩⟩
  · rw [← hmap0]
    refine prime_of _ ?_ hk0 (fun s hs => ?_)
    · have : Ideal.span {C ϖ, (X 1 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 0 ^ q} = RingHom.ker Ψ₀ := by
        ext s; rw [RingHom.mem_ker]; exact mem_span₀_iff red K ϖ hϖ s
      rw [this]; exact RingHom.ker_isPrime _
    · rw [RingHom.mem_ker, ← eval_ψ₀, (mem_span₀_iff red K ϖ hϖ s).mp hs, Polynomial.eval_zero]
  · rw [← hmap0]
    refine not_mem_of _ Ψ₀ (mem_span₀_iff red K ϖ hϖ) hk0 (fun s hs => by rw [hpe, ← eval_ψ₀, hs, Polynomial.eval_zero]) _ ?_
    rw [map_sub, map_pow]
    simp only [eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one]
    exact X_sub_X_pow_pow_ne_zero
  · rw [← hmap0]
    refine not_mem_of _ Ψ₀ (mem_span₀_iff red K ϖ hϖ) hk0 (fun s hs => by rw [hpe, ← eval_ψ₀, hs, Polynomial.eval_zero]) _ ?_
    rw [map_sub, eval₂Hom_C, RingHom.comp_apply]
    simp only [eval₂Hom_X', Matrix.cons_val_zero]
    intro h
    have h1 := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_zero] at h1
    exact one_ne_zero h1
  · rw [← hmap1]
    refine prime_of _ ?_ hk1 (fun s hs => ?_)
    · have : Ideal.span {C ϖ, (X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 1 ^ q} = RingHom.ker Ψ₁ := by
        ext s; rw [RingHom.mem_ker]; exact mem_span₁_iff red K ϖ hϖ s
      rw [this]; exact RingHom.ker_isPrime _
    · rw [RingHom.mem_ker, ← eval_ψ₁ red a K ha2, (mem_span₁_iff red K ϖ hϖ s).mp hs, Polynomial.eval_zero]
  · rw [← hmap1]
    refine not_mem_of _ Ψ₁ (mem_span₁_iff red K ϖ hϖ) hk1 (fun s hs => by rw [hpe, ← eval_ψ₁ red a K ha2, hs, Polynomial.eval_zero]) _ ?_
    rw [map_sub, map_pow]
    simp only [eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one]
    exact X_sub_X_pow_pow_ne_zero

end Branch
end NodeLocalized
end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint.ModularCurve _root_.ModularCurve.NodeLocalized _root_.P2MW.S_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint.ModularCurve.NodeLocalized in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    ((Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
        (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}).IsPrime ∧
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} ∧
      ∀ c : ↥(coeffSubring A K), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C c),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) ∧
    (a ^ (q ^ 2) = a →
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}).IsPrime ∧
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) :=
  ModularCurve.NodeLocalized.Branch.main red a K ϖ hϖ
end S_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint
end P2MW

public section
attribute [-instance] ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint
attribute [-simp] ModularCurve.NodeLocalized.coe_modularEvalAt
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.isPrime_span_uniformizer_branches_modularLocalizedAtPoint
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    ((Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
        (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}).IsPrime ∧
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} ∧
      ∀ c : ↥(coeffSubring A K), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C c),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) ∧
    (a ^ (q ^ 2) = a →
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}).IsPrime ∧
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint.solution
end
