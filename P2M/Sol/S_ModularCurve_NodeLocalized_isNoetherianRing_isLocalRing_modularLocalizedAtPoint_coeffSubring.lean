module

public import Definitions.Def_ModularCurve_NodeDescent
import P2M.Sol.S_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import P2M.Sol.S_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint
import P2M.Sol.S_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import P2M.Sol.S_ModularCurve_nonempty_modularPolynomialData
import P2M.Util
public import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

namespace P2MW.S_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
set_option autoImplicit false
set_option maxHeartbeats 3200000

p2m_open "ModularCurve P2MW.S_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring.ModularCurve.NodeLocalized"
open MvPolynomial

namespace ModularCurve
p2m_export "ModularCurve" "coeffMap coeffMap_coeff coeffEmb jqModC jqNModC map_jqModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jqN evalAtJ evalAtJ_X ModularPolynomialData NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero NodeLocalized.isPrime_span_uniformizer_branches_modularLocalizedAtPoint NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing nonempty_modularPolynomialData"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring redRestrict modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint modularEvalAt evalRange nodeDenominators ker_pointEval_eq_span pointEval_eq_zero_of_modularEval_eq_zero isPrime_span_uniformizer_branches_modularLocalizedAtPoint coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"
namespace N1

theorem isDVR {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] [CharP k q] [FiniteDimensional ℚ K] :
    IsDiscreteValuationRing ↥(coeffSubring A K) := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · exfalso
    have hqK : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
      rw [h]; exact (K.inv_mem (natCast_mem K q) : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ K)
    have h1 : redRestrict red K ((q : ℕ) : ↥(coeffSubring A K)) * redRestrict red K ⟨_, hqK⟩ = 1 := by
      rw [← map_mul, ← map_one (redRestrict red K)]
      congr 1
      apply Subtype.ext
      push_cast
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
    rw [map_natCast, CharP.cast_eq_zero, zero_mul] at h1
    exact zero_ne_one h1
  · exact h

variable {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ))

noncomputable def phiT (data : ModularPolynomialData q) : MvPolynomial (Fin 2) ↥(coeffSubring A K) :=
  Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom _)) (MvPolynomial.X 0))
    (MvPolynomial.X 1) data.Φ

theorem modularEval_phiT (data : ModularPolynomialData q) : modularEval (1 * q) (coeffSubring A K) (phiT A K data) = 0 := by
  set Qb := AlgebraicClosure ℚ
  set E : LaurentSeries ℚ →+* LaurentSeries Qb := coeffEmb Qb with hE
  set gJ : LaurentSeries Qb := coeffEmb Qb jq with hgJ
  set gJq : LaurentSeries Qb := coeffEmb Qb (qExpand ℚ (1 * q) jq) with hgJq
  set mE := modularEval (1 * q) (coeffSubring A K) with hmE
  set θ : Polynomial ℤ →+* LaurentSeries Qb := Polynomial.eval₂RingHom (Int.castRingHom _) gJ with hθ
  have hgen0 : mE (MvPolynomial.X 0) = gJ := by
    rw [hmE, modularEval, MvPolynomial.eval₂Hom_X', hgJ]
    show jqModC Qb = coeffMap (algebraMap ℚ Qb) (jqModC ℚ)
    exact (map_jqModC _).symm
  have hgen1 : mE (MvPolynomial.X 1) = gJq := by
    rw [hmE, modularEval, MvPolynomial.eval₂Hom_X', hgJq]
    show jqNModC Qb (1 * q) = coeffEmb Qb (qExpand ℚ (1 * q) jq)
    rw [jqNModC]
    have h1 : jqModC Qb = coeffEmb Qb jq := by
      show jqModC Qb = coeffMap (algebraMap ℚ Qb) (jqModC ℚ); exact (map_jqModC _).symm
    rw [h1]
    ext m
    unfold coeffEmb
    by_cases hm : ((1 * q : ℕ) : ℤ) ∣ m
    · obtain ⟨m', rfl⟩ := hm
      rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
    · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ hm, qExpand_coeff_of_not_dvd _ _ hm, map_zero]
  have hLHS : mE (phiT A K data) = data.Φ.eval₂ θ gJq := by
    rw [phiT, Polynomial.hom_eval₂, hgen1]
    congr 1
    apply Polynomial.ringHom_ext
    · intro n
      simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, hθ,
        map_intCast, eq_intCast]
    · rw [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hθ,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hgen0]
  have hq1 : E (jqN q) = gJq := by
    rw [hgJq, hE, jqN]
    congr 1
    simp only [one_mul]
  have hEJ : E.comp evalAtJ = θ := by
    apply Polynomial.ringHom_ext
    · intro n; simp only [RingHom.coe_comp, Function.comp_apply, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        map_intCast, eq_intCast]
    · rw [RingHom.coe_comp, Function.comp_apply, evalAtJ_X, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hgJ, hE]
  have hΦ : data.Φ.eval₂ θ gJq = 0 := by
    have h := congrArg E data.eval_eq_zero
    rw [map_zero, Polynomial.hom_eval₂, hEJ, hq1] at h
    exact h
  rw [hLHS, hΦ]

theorem phiT_ne_zero (data : ModularPolynomialData q) : phiT A K data ≠ 0 := by
  intro h

  let τ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* Polynomial ↥(coeffSubring A K) := eval₂Hom Polynomial.C ![0, Polynomial.X]
  have hτ : τ (phiT A K data) = data.Φ.map ((Polynomial.eval₂RingHom (Int.castRingHom ↥(coeffSubring A K)) 0)) := by
    rw [phiT, Polynomial.hom_eval₂]
    have hX : τ (MvPolynomial.X 1) = Polynomial.X := by
      show eval₂Hom Polynomial.C ![0, Polynomial.X] (MvPolynomial.X 1) = Polynomial.X
      rw [eval₂Hom_X']; rfl
    rw [hX]
    have hc : τ.comp (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom _)) (MvPolynomial.X 0))
        = Polynomial.C.comp (Polynomial.eval₂RingHom (Int.castRingHom ↥(coeffSubring A K)) 0) := by
      apply Polynomial.ringHom_ext
      · intro n
        simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
          map_intCast, eq_intCast]
      · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        show eval₂Hom Polynomial.C ![0, Polynomial.X] (MvPolynomial.X 0) = Polynomial.C 0
        rw [eval₂Hom_X', map_zero]; rfl
    rw [hc]; rfl
  have hm : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(coeffSubring A K)) 0)).Monic := data.monic.map _
  have h0 : τ (phiT A K data) = 0 := by rw [h, map_zero]
  rw [hτ] at h0
  exact hm.ne_zero h0

section Main
variable [FiniteDimensional ℚ K] [DecidableEq k]

theorem main (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ∧ IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ∧ ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = 2 ∧
    (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))], IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
      Ideal.span {modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C ϖ), modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.C x),
        modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))}) := by
  classical
  haveI hfact : Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K)) ≤
      RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
    ⟨fun s hs => (RingHom.mem_ker).mpr
      (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s ((RingHom.mem_ker).mp hs))⟩
  haveI : IsDiscreteValuationRing ↥(coeffSubring A K) := isDVR red K q
  set φ := modularEval (1 * q) (coeffSubring A K) with hφ
  set pe := pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) with hpe
  set E := modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) with hEdef
  set ρ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(evalRange (1 * q) (coeffSubring A K)) := φ.rangeRestrict with hρ
  have hρsurj : Function.Surjective ρ := RingHom.rangeRestrict_surjective φ
  have hkerρ : RingHom.ker ρ = RingHom.ker φ := RingHom.ker_rangeRestrict φ
  have hEρ : (algebraMap (↥(evalRange (1 * q) (coeffSubring A K))) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))).comp ρ = E := RingHom.ext fun _ => rfl

  haveI : IsNoetherianRing ↥(evalRange (1 * q) (coeffSubring A K)) := isNoetherianRing_of_surjective _ _ ρ hρsurj
  have hnoeth : IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    IsLocalization.isNoetherianRing (nodeDenominators (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) _ ‹_›
  have hloc : IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := inferInstance

  haveI : (RingHom.ker pe).IsPrime := RingHom.ker_isPrime pe
  set P : Ideal ↥(evalRange (1 * q) (coeffSubring A K)) := (RingHom.ker pe).map ρ with hP
  haveI hPp : P.IsPrime := Ideal.map_isPrime_of_surjective hρsurj (by rw [hkerρ]; exact hfact.out)
  have hM : nodeDenominators (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) = P.primeCompl := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩ hy
      obtain ⟨s', hs', hss'⟩ := (Ideal.mem_map_iff_of_surjective ρ hρsurj).mp hy
      have hd : s - s' ∈ RingHom.ker φ := by
        rw [← hkerρ, RingHom.mem_ker, map_sub, sub_eq_zero]; exact hss'.symm
      have : s ∈ RingHom.ker pe := by simpa using (RingHom.ker pe).add_mem (hfact.out hd) hs'
      exact hs ((RingHom.mem_ker).mp this)
    · intro hy
      obtain ⟨s, rfl⟩ := hρsurj y
      refine ⟨s, fun hs0 => hy (Ideal.mem_map_of_mem ρ ((RingHom.mem_ker).mpr hs0)), rfl⟩
  haveI : IsLocalization.AtPrime (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) P := by
    show IsLocalization P.primeCompl _
    rw [← hM]; infer_instance

  have hker : RingHom.ker pe = Ideal.span {MvPolynomial.C ϖ, MvPolynomial.X 0 - MvPolynomial.C x,
      MvPolynomial.X 1 - MvPolynomial.C (x ^ q)} :=
    ker_pointEval_eq_span (coeffSubring A K) (redRestrict red K) a (a ^ q) x (x ^ q) hx (by rw [map_pow, hx]) ϖ hϖ
  have hmaxEq : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
      Ideal.span {E (MvPolynomial.C ϖ), E (MvPolynomial.X 0 - MvPolynomial.C x), E (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), hP, Ideal.map_map, hEρ, hker, Ideal.map_span,
      Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData q
  have hΦk : phiT A K data ∈ RingHom.ker φ := modularEval_phiT A K data
  have hΦ0 : phiT A K data ≠ 0 := phiT_ne_zero A K data
  have hdimS : ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K)) = 3 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one, Nat.card_fin]; rfl
  have h1 : ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K) ⧸ Ideal.span {phiT A K data}) + 1 ≤ 3 :=
    hdimS ▸ ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hΦ0)
  have h2 : ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K) ⧸ RingHom.ker φ) ≤ ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K) ⧸ Ideal.span {phiT A K data}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor
      ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hΦk)))) (Ideal.Quotient.factor_surjective _)
  have h3 : ringKrullDim ↥(evalRange (1 * q) (coeffSubring A K)) = ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K) ⧸ RingHom.ker φ) :=
    (ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivRange φ)).symm

  have hRR : ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ≤ ringKrullDim ↥(evalRange (1 * q) (coeffSubring A K)) := by
    refine Order.krullDim_le_of_strictMono
      (fun p : PrimeSpectrum ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =>
        (⟨p.asIdeal.comap (algebraMap (↥(evalRange (1 * q) (coeffSubring A K))) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))), inferInstance⟩ : PrimeSpectrum ↥(evalRange (1 * q) (coeffSubring A K)))) ?_
    intro p p' hlt
    refine lt_of_le_of_ne (Ideal.comap_mono hlt.le) ?_
    intro heq
    apply hlt.ne
    apply PrimeSpectrum.ext
    have heq' : Ideal.comap (algebraMap (↥(evalRange (1 * q) (coeffSubring A K))) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) p.asIdeal
        = Ideal.comap (algebraMap (↥(evalRange (1 * q) (coeffSubring A K))) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) p'.asIdeal :=
      congrArg PrimeSpectrum.asIdeal heq
    have hmc1 : Ideal.map (algebraMap (↥(evalRange (1 * q) (coeffSubring A K))) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))))
        (Ideal.comap (algebraMap (↥(evalRange (1 * q) (coeffSubring A K))) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) p.asIdeal) = p.asIdeal :=
      IsLocalization.map_comap (nodeDenominators (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) p.asIdeal
    have hmc2 : Ideal.map (algebraMap (↥(evalRange (1 * q) (coeffSubring A K))) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))))
        (Ideal.comap (algebraMap (↥(evalRange (1 * q) (coeffSubring A K))) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) p'.asIdeal) = p'.asIdeal :=
      IsLocalization.map_comap (nodeDenominators (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) p'.asIdeal
    rw [← hmc1, ← hmc2, heq']
  have hup : ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) + 1 ≤ 3 := by
    have : ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ≤ ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K) ⧸ Ideal.span {phiT A K data}) :=
      hRR.trans (h3 ▸ h2)
    exact (add_le_add this le_rfl).trans h1

  obtain ⟨⟨hp1, -, hnot⟩, -⟩ :=
    ModularCurve.NodeLocalized.isPrime_span_uniformizer_branches_modularLocalizedAtPoint red a K ϖ hϖ
  set 𝔭₁ : Ideal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := Ideal.span {E (MvPolynomial.C ϖ), E (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)} with h𝔭₁
  haveI : 𝔭₁.IsPrime := hp1
  have hϖ0 : E (MvPolynomial.C ϖ) ≠ 0 := by
    intro h
    have h1 : (ϖ : AlgebraicClosure ℚ) = 0 := by
      have := congrArg (fun w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) => (w : LaurentSeries (AlgebraicClosure ℚ))) h
      change modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ) = 0 at this
      rw [modularEval, MvPolynomial.eval₂Hom_C] at this
      change algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ) = 0 at this
      exact (map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective).mp this
    have h2 : ϖ = 0 := Subtype.ext h1
    have h3 : redRestrict red K ((q : ℕ) : ↥(coeffSubring A K)) = 0 := by rw [map_natCast, CharP.cast_eq_zero]
    obtain ⟨d, hd⟩ := (hϖ _).mp h3
    rw [h2, zero_mul] at hd
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
      (by have := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hd; push_cast at this; exact this)
  have hbot : (⊥ : Ideal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) < 𝔭₁ :=
    bot_lt_iff_ne_bot.mpr fun h => hϖ0 (by
      have : E (MvPolynomial.C ϖ) ∈ 𝔭₁ := Ideal.subset_span (Set.mem_insert _ _)
      rw [h] at this; exact (Submodule.mem_bot _).mp this)
  have hlt : 𝔭₁ < IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp1.ne_top) fun h => hnot x ?_
    change E (MvPolynomial.X 0 - MvPolynomial.C x) ∈ 𝔭₁
    rw [h, hmaxEq]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hlow : (2 : WithBot ℕ∞) ≤ ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
    let p0 : PrimeSpectrum ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := ⟨⊥, Ideal.bot_prime⟩
    let p1 : PrimeSpectrum ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := ⟨𝔭₁, hp1⟩
    let p2 : PrimeSpectrum ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := ⟨IsLocalRing.maximalIdeal _, inferInstance⟩
    have h01 : p0 < p1 := hbot
    have h12 : p1 < p2 := hlt
    let s : LTSeries (PrimeSpectrum ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
      { length := 2
        toFun := ![p0, p1, p2]
        step := fun i => by
          fin_cases i
          · exact h01
          · exact h12 }
    calc (2 : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by norm_num
      _ = (s.length : WithBot ℕ∞) := rfl
      _ ≤ _ := Order.LTSeries.length_le_krullDim s
  have hdim : ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = 2 := by
    have hup' : ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ≤ 2 := by
      revert hup
      generalize ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = d
      intro hup
      induction d using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe e =>
        induction e using ENat.recTopCoe with
        | top => exact absurd hup (by decide)
        | coe m =>
          have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((3 : ℕ) : WithBot ℕ∞) := by simpa using hup
          have h3' : m + 1 ≤ 3 := by exact_mod_cast h'
          have hm : (m : ℕ∞) ≤ 2 := by exact_mod_cast (by omega : m ≤ 2)
          exact WithBot.coe_le_coe.mpr hm
    exact le_antisymm hup' hlow
  exact ⟨hnoeth, hloc, hdim, fun {_} => hmaxEq⟩

end Main

end N1
end NodeLocalized
end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring.ModularCurve _root_.ModularCurve.NodeLocalized _root_.P2MW.S_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring.ModularCurve.NodeLocalized in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ∧
    IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ∧
    ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = 2 ∧
    (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
      IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) :=
  ModularCurve.NodeLocalized.N1.main A red a K x hx ϖ hϖ
end S_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
end P2MW

public section
attribute [-instance] ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint
attribute [-simp] ModularCurve.NodeLocalized.coe_modularEvalAt
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ∧
    IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ∧
    ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = 2 ∧
    (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
      IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring.solution
end
