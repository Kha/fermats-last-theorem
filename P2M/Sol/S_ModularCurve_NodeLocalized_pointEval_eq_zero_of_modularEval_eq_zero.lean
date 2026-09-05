module

public import Mathlib
public import Definitions.Def_ModularCurve_NodeLocalized
public import Definitions.Def_ModularCurve_NodeDescent
public import Definitions.Def_ModularCurve_FibrePoly
public import Theorems.Thm_ModularCurve_exists_phiIrreducible
public import Theorems.Thm_ModularCurve_minpoly_jqNModC_eq
public import Theorems.Thm_ModularCurve_transcendental_jqModC
public import Theorems.Thm_ModularCurve_kroneckerCongruence
public import Theorems.Thm_ModularCurve_fibrePoly_eq_of_kroneckerCongruence
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized ModularCurve.PhiGen Polynomial

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (s : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hs : modularEval (1 * q) (coeffSubring A K) s = 0) :
    pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s = 0 := by
  classical
  have hqP : q.Prime := Fact.out
  haveI hq1 : Fact (Nat.Prime (1 * q)) := ⟨by rw [one_mul]; exact hqP⟩
  haveI : CharP k (1 * q) := by rw [one_mul]; infer_instance
  obtain ⟨data, -⟩ := ModularCurve.exists_phiIrreducible (1 * q)

  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* Polynomial (Polynomial ↥(coeffSubring A K)),
      ψ = MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C) ![Polynomial.C Polynomial.X, Polynomial.X] := ⟨_, rfl⟩
  obtain ⟨EV, hEVd⟩ : ∃ EV : Polynomial (Polynomial ↥(coeffSubring A K)) →+* LaurentSeries (AlgebraicClosure ℚ),
      EV = Polynomial.eval₂RingHom
        (Polynomial.eval₂RingHom (CharPReduction.constSeries (coeffSubring A K)) (jqModC (AlgebraicClosure ℚ)))
        (jqNModC (AlgebraicClosure ℚ) (1 * q)) := ⟨_, rfl⟩
  obtain ⟨PT, hPTd⟩ : ∃ PT : Polynomial (Polynomial ↥(coeffSubring A K)) →+* k,
      PT = Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (redRestrict red K) a) (a ^ q) := ⟨_, rfl⟩
  have hEV : (modularEval (1 * q) (coeffSubring A K) : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* _) = EV.comp ψ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [modularEval, hψ, hEVd]
    · fin_cases i <;> simp [modularEval, hψ, hEVd]
  have hPT : (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* k) = PT.comp ψ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [pointEval, hψ, hPTd]
    · fin_cases i <;> simp [pointEval, hψ, hPTd]

  let ΦR : Polynomial (Polynomial ↥(coeffSubring A K)) := data.Φ.map (Polynomial.mapRingHom (Int.castRingHom ↥(coeffSubring A K)))
  have hΦmonic : ΦR.Monic := data.monic.map _

  let F := IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))
  let jF : ↥F := ⟨jqModC (AlgebraicClosure ℚ), IntermediateField.mem_adjoin_simple_self _ _⟩
  let ι : ↥(coeffSubring A K) →+* AlgebraicClosure ℚ := (coeffSubring A K).subtype
  obtain ⟨θ₀, hθ₀d⟩ : ∃ θ₀ : Polynomial ↥(coeffSubring A K) →+* ↥F,
      θ₀ = Polynomial.eval₂RingHom ((algebraMap (AlgebraicClosure ℚ) ↥F).comp ι) jF := ⟨_, rfl⟩
  obtain ⟨θ, hθd⟩ : ∃ θ : Polynomial (Polynomial ↥(coeffSubring A K)) →+* Polynomial ↥F,
      θ = Polynomial.mapRingHom θ₀ := ⟨_, rfl⟩

  have hθ₀L : (algebraMap ↥F (LaurentSeries (AlgebraicClosure ℚ))).comp θ₀
      = Polynomial.eval₂RingHom (CharPReduction.constSeries (coeffSubring A K)) (jqModC (AlgebraicClosure ℚ)) := by
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · simp [hθ₀d, ι, CharPReduction.constSeries]
    · simp [hθ₀d, jF]
  have hEVθ : EV = (Polynomial.eval₂RingHom (algebraMap ↥F (LaurentSeries (AlgebraicClosure ℚ)))
      (jqNModC (AlgebraicClosure ℚ) (1 * q))).comp θ := by
    refine Polynomial.ringHom_ext (fun p => ?_) ?_
    · rw [hEVd, hθd]
      simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C]
      exact (congrArg (fun g : Polynomial ↥(coeffSubring A K) →+* _ => g p) hθ₀L).symm
    · rw [hEVd, hθd]; simp

  have hθ₀ : Function.Injective θ₀ := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have h1 : (θ₀ p : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [hp]; rfl
    have h2 : (θ₀ p : LaurentSeries (AlgebraicClosure ℚ))
        = Polynomial.aeval (jqModC (AlgebraicClosure ℚ)) (p.map ι) := by
      have := congrArg (fun g : Polynomial ↥(coeffSubring A K) →+* _ => g p) hθ₀L
      simp only [RingHom.coe_comp, Function.comp_apply] at this
      rw [show ((θ₀ p : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) = algebraMap ↥F _ (θ₀ p) from rfl, this,
        Polynomial.coe_eval₂RingHom, Polynomial.aeval_def, Polynomial.eval₂_map]
      rfl
    rw [h2] at h1
    have h3 : p.map ι = 0 :=
      (transcendental_iff_injective.mp (ModularCurve.transcendental_jqModC (AlgebraicClosure ℚ)))
        (by rw [h1, map_zero])
    exact (Polynomial.map_injective ι Subtype.val_injective) (by rw [h3, Polynomial.map_zero])
  have hθ : Function.Injective θ := by rw [hθd]; exact Polynomial.map_injective θ₀ hθ₀

  have hθΦ : θ ΦR = minpoly ↥F (jqNModC (AlgebraicClosure ℚ) (1 * q)) := by
    rw [ModularCurve.minpoly_jqNModC_eq (AlgebraicClosure ℚ) (1 * q) data]
    simp only [hθd, ΦR, Polynomial.coe_mapRingHom, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [hθ₀d, jF]

  set p := ψ s with hp
  have hEVp : EV p = 0 := by
    have := congrArg (fun g : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* _ => g s) hEV
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    rw [← this]; exact hs
  have hEVΦ : EV ΦR = 0 := by
    rw [hEVθ, RingHom.comp_apply, hθΦ, Polynomial.coe_eval₂RingHom, ← Polynomial.aeval_def]
    exact minpoly.aeval ↥F _
  set r := p %ₘ ΦR with hr
  have hEVr : EV r = 0 := by
    have hdiv := Polynomial.modByMonic_add_div p ΦR
    have := congrArg EV hdiv
    rw [map_add, map_mul, hEVΦ, zero_mul, add_zero, hEVp] at this
    exact this
  have hr0 : r = 0 := by
    apply hθ
    rw [map_zero]
    by_contra hne
    have haeval : Polynomial.aeval (jqNModC (AlgebraicClosure ℚ) (1 * q)) (θ r) = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.coe_eval₂RingHom, ← RingHom.comp_apply, ← hEVθ]
      exact hEVr
    have hle := minpoly.degree_le_of_ne_zero ↥F (jqNModC (AlgebraicClosure ℚ) (1 * q)) hne haeval
    have hlt : (θ r).degree < (minpoly ↥F (jqNModC (AlgebraicClosure ℚ) (1 * q))).degree := by
      rw [← hθΦ]
      calc (θ r).degree ≤ r.degree := by rw [hθd]; exact Polynomial.degree_map_le
        _ < ΦR.degree := Polynomial.degree_modByMonic_lt p hΦmonic
        _ = (θ ΦR).degree := by rw [hθd]; exact (hΦmonic.degree_map θ₀).symm
    exact absurd hle (not_le.mpr hlt)
  have hfac : p = ΦR * (p /ₘ ΦR) := by
    have hdiv := Polynomial.modByMonic_add_div p ΦR
    rw [← hr, hr0, zero_add] at hdiv
    exact hdiv.symm

  have hPTΦ : PT ΦR = 0 := by
    have hK := ModularCurve.kroneckerCongruence (1 * q) data
    have hfib := ModularCurve.fibrePoly_eq_of_kroneckerCongruence (k := k) data hK a
    have h1 : PT ΦR = (ModularCurve.fibrePoly data.Φ a).eval (a ^ q) := by
      rw [hPTd, Polynomial.coe_eval₂RingHom]
      simp only [ΦR, ModularCurve.fibrePoly, Polynomial.eval_map, Polynomial.eval₂_map]
      congr 1
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp
    rw [h1, hfib]
    simp

  have := congrArg (fun g : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* k => g s) hPT
  simp only [RingHom.coe_comp, Function.comp_apply] at this
  rw [this, ← hp, hfac, map_mul, hPTΦ, zero_mul]
