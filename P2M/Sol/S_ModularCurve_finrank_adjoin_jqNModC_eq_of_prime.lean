module

public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Sol.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank
import P2M.Sol.S_AlgebraicCurve_Place_inertiaDeg_pos
import P2M.Sol.S_ModularCurve_transcendental_jqModC
import P2M.Sol.S_ModularCurve_coeffEmb_jq
import P2M.Sol.S_ModularCurve_laurentBaseChange_modularFunctionField
import P2M.Sol.S_ModularCurve_full_eq_of_prime
import P2M.Sol.S_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import P2M.Sol.S_ModularCurve_finrank_adjoin_jqNModC_le
import P2M.Sol.S_ModularCurve_finiteDimensional_adjoin_jqNModC
import P2M.Sol.S_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import P2M.Sol.S_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import P2M.Sol.S_ModularCurve_cuspZeroBar_ne_cuspInftyBar
import P2M.Sol.S_ModularCurve_isCusp_cuspZeroBar
import P2M.Sol.S_ModularCurve_isCusp_cuspInftyBar
import P2M.Sol.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import P2M.Util
public import Definitions.Def_ModularCurve_JqCoeff
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum

namespace P2MW.S_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

p2m_open "ModularCurve~dedekindPsi_prime AlgebraicCurve IntermediateField"
open scoped Polynomial

noncomputable section

namespace DegAux

local notation "𝕂" => AlgebraicClosure ℚ

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem prime' : ℓ.Prime := Fact.out

theorem dedekindPsi_prime : dedekindPsi ℓ = ℓ + 1 := by
  have hℓ : ℓ.Prime := Fact.out
  rw [dedekindPsi, hℓ.divisors, Finset.filter_true_of_mem, Finset.sum_pair hℓ.one_lt.ne, Nat.div_one,
    Nat.div_self hℓ.pos, add_comm]
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact squarefree_one
  · exact hℓ.squarefree

def jb : modularFunctionFieldBar ℓ := ⟨coeffEmb 𝕂 jq, coeffEmb_mem_laurentBaseChange 𝕂 (jq_mem_full ℓ)⟩

theorem coe_jb : (jb ℓ : LaurentSeries 𝕂) = jqModC 𝕂 := coeffEmb_jq 𝕂

theorem bar_eq_restrictScalars :
    modularFunctionFieldBar ℓ = (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯).restrictScalars 𝕂 := by
  have hℓ : ℓ.Prime := Fact.out
  show laurentBaseChange 𝕂 (modularFunctionFieldFull ℓ) = _
  rw [full_eq_of_prime hℓ, laurentBaseChange_modularFunctionField]
  exact (adjoin_simple_adjoin_simple 𝕂 (jqModC 𝕂) (jqNModC 𝕂 ℓ)).symm

def σa : RatFunc 𝕂 ≃ₐ[𝕂] 𝕂⟮jqModC 𝕂⟯ :=
  RatFunc.algEquivOfTranscendental (jqModC 𝕂) (transcendental_jqModC 𝕂)

theorem coe_σa_X : ((σa (RatFunc.X : RatFunc 𝕂) : 𝕂⟮jqModC 𝕂⟯) : LaurentSeries 𝕂) = jqModC 𝕂 :=
  RatFunc.algEquivOfTranscendental_X (jqModC 𝕂) (transcendental_jqModC 𝕂)

theorem mem_bar_iff (x : LaurentSeries 𝕂) :
    x ∈ modularFunctionFieldBar ℓ ↔ x ∈ 𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯ := by
  rw [bar_eq_restrictScalars ℓ, mem_restrictScalars]

def jTr : (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) ≃+* modularFunctionFieldBar ℓ where
  toFun x := ⟨x, (mem_bar_iff ℓ _).mpr x.2⟩
  invFun y := ⟨y, (mem_bar_iff ℓ _).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem coe_jTr (x : 𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) :
    ((jTr ℓ x : modularFunctionFieldBar ℓ) : LaurentSeries 𝕂) = x := by
  unfold jTr; rfl

def φ : RatFunc 𝕂 →+* modularFunctionFieldBar ℓ :=
  (jTr ℓ).toRingHom.comp
    ((algebraMap (𝕂⟮jqModC 𝕂⟯) (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯)).comp (σa).toRingEquiv.toRingHom)

theorem φ_apply (x : RatFunc 𝕂) :
    φ ℓ x = jTr ℓ (algebraMap (𝕂⟮jqModC 𝕂⟯) (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) (σa x)) := rfl

theorem coe_algebraMap_tower (y : 𝕂⟮jqModC 𝕂⟯) :
    ((algebraMap (𝕂⟮jqModC 𝕂⟯) (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) y : 𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) :
      LaurentSeries 𝕂) = y := rfl

theorem coe_φ (x : RatFunc 𝕂) :
    ((φ ℓ x : modularFunctionFieldBar ℓ) : LaurentSeries 𝕂) = (σa x : LaurentSeries 𝕂) := by
  rw [φ_apply, coe_jTr, coe_algebraMap_tower]

theorem φ_algebraMap (k : 𝕂) : φ ℓ (algebraMap 𝕂 (RatFunc 𝕂) k) = algebraMap 𝕂 (modularFunctionFieldBar ℓ) k := by
  apply Subtype.ext
  rw [coe_φ, AlgEquiv.commutes]
  rfl

theorem φ_X : φ ℓ (RatFunc.X : RatFunc 𝕂) = jb ℓ := by
  apply Subtype.ext
  rw [coe_φ, coe_jb, coe_σa_X]

abbrev algRatFunc : Algebra (RatFunc 𝕂) (modularFunctionFieldBar ℓ) := (φ ℓ).toAlgebra

attribute [local instance] algRatFunc

theorem algebraMap_eq : algebraMap (RatFunc 𝕂) (modularFunctionFieldBar ℓ) = φ ℓ := rfl

theorem isScalarTower_ratFunc : IsScalarTower 𝕂 (RatFunc 𝕂) (modularFunctionFieldBar ℓ) :=
  IsScalarTower.of_algebraMap_eq fun k => (φ_algebraMap ℓ k).symm

attribute [local instance] isScalarTower_ratFunc

theorem he_compat :
    (algebraMap (RatFunc 𝕂) (modularFunctionFieldBar ℓ)).comp
        (σa.symm.toRingEquiv : 𝕂⟮jqModC 𝕂⟯ ≃+* RatFunc 𝕂).toRingHom
      = (jTr ℓ).toRingHom.comp (algebraMap (𝕂⟮jqModC 𝕂⟯) (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯)) := by
  apply RingHom.ext
  intro y
  show φ ℓ (σa.symm y) = jTr ℓ (algebraMap _ _ y)
  rw [φ_apply, AlgEquiv.apply_symm_apply]

theorem finite_ratFunc : Module.Finite (RatFunc 𝕂) (modularFunctionFieldBar ℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree ℓ hℓ.squarefree hℓ.one_lt
  haveI := finiteDimensional_adjoin_jqNModC 𝕂 data
  exact Module.Finite.of_equiv_equiv (σa.symm.toRingEquiv : 𝕂⟮jqModC 𝕂⟯ ≃+* RatFunc 𝕂) (jTr ℓ)
    (he_compat ℓ)

attribute [local instance] finite_ratFunc

theorem finrank_le : Module.finrank (RatFunc 𝕂) (modularFunctionFieldBar ℓ) ≤ ℓ + 1 := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree ℓ hℓ.squarefree hℓ.one_lt
  rw [← Algebra.finrank_eq_of_equiv_equiv (σa.symm.toRingEquiv : 𝕂⟮jqModC 𝕂⟯ ≃+* RatFunc 𝕂) (jTr ℓ)
    (he_compat ℓ), ← dedekindPsi_prime ℓ]
  exact finrank_adjoin_jqNModC_le 𝕂 data

theorem isSeparable_ratFunc : Algebra.IsSeparable (RatFunc 𝕂) (modularFunctionFieldBar ℓ) :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

attribute [local instance] isSeparable_ratFunc

theorem restrict_eq_of_isCusp (u : Place 𝕂 (modularFunctionFieldBar ℓ)) (hu : IsCusp (jb ℓ) u) :
    u.restrict (RatFunc 𝕂) = (cuspInftyBar ℓ).restrict (RatFunc 𝕂) := by
  have key : ∀ u' : Place 𝕂 (modularFunctionFieldBar ℓ), IsCusp (jb ℓ) u' →
      ∀ p : IsDedekindDomain.HeightOneSpectrum 𝕂[X],
        u'.restrict (RatFunc 𝕂) ≠ Place.ofHeightOneSpectrum p := by
    intro u' hu' p heq
    apply hu'
    have hX : (RatFunc.X : RatFunc 𝕂) ∈ (u'.restrict (RatFunc 𝕂)).toValuationSubring := by
      rw [heq, Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff,
        ← RatFunc.algebraMap_X]
      exact p.valuation_le_one _
    rw [Place.mem_restrict_iff, algebraMap_eq, φ_X] at hX
    exact hX
  exact RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum (key u hu)
    (key _ (isCusp_cuspInftyBar ℓ))

theorem e_infty : ((cuspInftyBar ℓ).ramificationIndex (RatFunc 𝕂) : ℤ) = 1 ∧
    ((cuspInftyBar ℓ).restrict (RatFunc 𝕂)).ord RatFunc.X = -1 := by
  have h := (cuspInftyBar ℓ).ord_restrict (F := RatFunc 𝕂) RatFunc.X
  rw [algebraMap_eq, φ_X] at h
  have hj : (cuspInftyBar ℓ).ord (jb ℓ) = -1 := ord_cuspInftyBar_coeffEmb_jq ℓ
  rw [hj] at h
  have epos : (0 : ℤ) < (cuspInftyBar ℓ).ramificationIndex (RatFunc 𝕂) := by
    exact_mod_cast (cuspInftyBar ℓ).ramificationIndex_pos (F := RatFunc 𝕂)
  have h1 : ((cuspInftyBar ℓ).ramificationIndex (RatFunc 𝕂) : ℤ) *
      (-((cuspInftyBar ℓ).restrict (RatFunc 𝕂)).ord RatFunc.X) = 1 := by linarith
  have he := Int.eq_one_of_mul_eq_one_right epos.le h1
  refine ⟨he, ?_⟩
  rw [he, one_mul] at h1
  linarith

theorem e_zero (hw : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ)) :
    ((cuspZeroBar ℓ).ramificationIndex (RatFunc 𝕂) : ℤ) = ℓ := by
  have h := (cuspZeroBar ℓ).ord_restrict (F := RatFunc 𝕂) RatFunc.X
  rw [algebraMap_eq, φ_X, restrict_eq_of_isCusp ℓ _ (isCusp_cuspZeroBar ℓ hw), (e_infty ℓ).2] at h
  have hj : (cuspZeroBar ℓ).ord (jb ℓ) = -ℓ := ord_cuspZeroBar_coeffEmb_jq ℓ hw
  rw [hj] at h
  linarith

theorem eq_cuspInftyBar_or_eq_cuspZeroBar (hw : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ))
    (w : Place 𝕂 (modularFunctionFieldBar ℓ)) (hc : IsCusp (jb ℓ) w) :
    w = cuspInftyBar ℓ ∨ w = cuspZeroBar ℓ := by
  classical
  by_contra hnot
  have h1 : w ≠ cuspInftyBar ℓ := fun h => hnot (Or.inl h)
  have h2 : w ≠ cuspZeroBar ℓ := fun h => hnot (Or.inr h)
  have hℓ : ℓ.Prime := Fact.out
  have hne : cuspZeroBar ℓ ≠ cuspInftyBar ℓ := cuspZeroBar_ne_cuspInftyBar ℓ hw hℓ.one_lt
  have r0 := restrict_eq_of_isCusp ℓ _ (isCusp_cuspZeroBar ℓ hw)
  have rw' := restrict_eq_of_isCusp ℓ _ hc
  have hS : ∀ u ∈ ({cuspInftyBar ℓ, cuspZeroBar ℓ, w} : Finset (Place 𝕂 (modularFunctionFieldBar ℓ))),
      u.restrict (RatFunc 𝕂) = (cuspInftyBar ℓ).restrict (RatFunc 𝕂) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · rfl
    · exact r0
    · exact rw'
  have hsum := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank _ _ hS
  rw [Finset.sum_insert (by simp [hne.symm, Ne.symm h1]), Finset.sum_insert (by simp [Ne.symm h2]),
    Finset.sum_singleton] at hsum
  have hrank : (Module.finrank (RatFunc 𝕂) (modularFunctionFieldBar ℓ) : ℤ) ≤ ℓ + 1 := by
    exact_mod_cast finrank_le ℓ
  have e1 := (e_infty ℓ).1
  have e0 := e_zero ℓ hw
  have ew : (1 : ℤ) ≤ w.ramificationIndex (RatFunc 𝕂) := by
    exact_mod_cast w.ramificationIndex_pos (F := RatFunc 𝕂)
  have f1 : (1 : ℤ) ≤ (cuspInftyBar ℓ).inertiaDeg (RatFunc 𝕂) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc 𝕂) (cuspInftyBar ℓ)
  have f0 : (1 : ℤ) ≤ (cuspZeroBar ℓ).inertiaDeg (RatFunc 𝕂) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc 𝕂) (cuspZeroBar ℓ)
  have fw : (1 : ℤ) ≤ w.inertiaDeg (RatFunc 𝕂) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc 𝕂) w
  have p0 : (ℓ : ℤ) ≤ ((cuspZeroBar ℓ).ramificationIndex (RatFunc 𝕂) : ℤ) *
      ((cuspZeroBar ℓ).inertiaDeg (RatFunc 𝕂) : ℤ) := by
    rw [e0]; nlinarith
  have pw : (1 : ℤ) ≤ (w.ramificationIndex (RatFunc 𝕂) : ℤ) * (w.inertiaDeg (RatFunc 𝕂) : ℤ) :=
    one_le_mul_of_one_le_of_one_le ew fw
  rw [e1, one_mul] at hsum
  linarith

theorem le_finrank : ℓ + 1 ≤ Module.finrank (RatFunc 𝕂) (modularFunctionFieldBar ℓ) := by
  classical
  have hw := isFrickeAutFull_frickeInvolutionFull_prime ℓ
  have hℓ : ℓ.Prime := Fact.out
  have hne : cuspZeroBar ℓ ≠ cuspInftyBar ℓ := cuspZeroBar_ne_cuspInftyBar ℓ hw hℓ.one_lt
  have r0 := restrict_eq_of_isCusp ℓ _ (isCusp_cuspZeroBar ℓ hw)
  have hS : ∀ u ∈ ({cuspInftyBar ℓ, cuspZeroBar ℓ} : Finset (Place 𝕂 (modularFunctionFieldBar ℓ))),
      u.restrict (RatFunc 𝕂) = (cuspInftyBar ℓ).restrict (RatFunc 𝕂) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · rfl
    · exact r0
  have hsum := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank _ _ hS
  rw [Finset.sum_insert (by simp [hne.symm]), Finset.sum_singleton] at hsum
  have e1 := (e_infty ℓ).1
  have e0 := e_zero ℓ hw
  have f1 : (1 : ℤ) ≤ (cuspInftyBar ℓ).inertiaDeg (RatFunc 𝕂) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc 𝕂) (cuspInftyBar ℓ)
  have f0 : (1 : ℤ) ≤ (cuspZeroBar ℓ).inertiaDeg (RatFunc 𝕂) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc 𝕂) (cuspZeroBar ℓ)
  have p0 : (ℓ : ℤ) ≤ ((cuspZeroBar ℓ).ramificationIndex (RatFunc 𝕂) : ℤ) *
      ((cuspZeroBar ℓ).inertiaDeg (RatFunc 𝕂) : ℤ) := by
    rw [e0]; nlinarith
  rw [e1, one_mul] at hsum
  have : ((ℓ + 1 : ℕ) : ℤ) ≤ (Module.finrank (RatFunc 𝕂) (modularFunctionFieldBar ℓ) : ℤ) := by
    push_cast; linarith
  exact_mod_cast this

theorem finrank_tower_eq : Module.finrank (𝕂⟮jqModC 𝕂⟯) (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) =
    Module.finrank (RatFunc 𝕂) (modularFunctionFieldBar ℓ) :=
  Algebra.finrank_eq_of_equiv_equiv (σa.symm.toRingEquiv : 𝕂⟮jqModC 𝕂⟯ ≃+* RatFunc 𝕂) (jTr ℓ) (he_compat ℓ)

end DegAux

open DegAux in

theorem solution (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))) (IntermediateField.adjoin (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))) ({jqNModC (AlgebraicClosure ℚ) ℓ} : Set (LaurentSeries (AlgebraicClosure ℚ)))) = ℓ + 1 := by
  apply le_antisymm
  · have hℓ : ℓ.Prime := Fact.out
    obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree ℓ hℓ.squarefree hℓ.one_lt
    simpa [DegAux.dedekindPsi_prime ℓ] using finrank_adjoin_jqNModC_le (AlgebraicClosure ℚ) data
  · have h := DegAux.le_finrank ℓ
    rw [← DegAux.finrank_tower_eq ℓ] at h
    exact h
end
end S_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime
end P2MW

public section
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single
attribute [-simp] AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open ModularCurve

theorem ModularCurve.finrank_adjoin_jqNModC_eq_of_prime (ℓ : ℕ) [Fact ℓ.Prime] : Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))) (IntermediateField.adjoin (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))) ({jqNModC (AlgebraicClosure ℚ) ℓ} : Set (LaurentSeries (AlgebraicClosure ℚ)))) = ℓ + 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime.solution
end
