module

public import Mathlib
public import Definitions.Def_ModularCurve_NodeLocalized
public import Definitions.Def_ModularCurve_NodeDescent
public import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
public import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
public import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
public import Theorems.Thm_ModularCurve_isPrime_span_uniformizer_and_maximalIdeal_modularLocalizedAtPoint_eq_of_pow_sq_ne
public import Theorems.Thm_IsLocalRing_isIntegrallyClosed_of_isPrincipalIdealRing_quotient
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne.ModularCurve"
open ModularCurve.NodeLocalized

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring isPrime_span_uniformizer_and_maximalIdeal_modularLocalizedAtPoint_eq_of_pow_sq_ne"
p2m_open "ModularCurve"
namespace RegRIC

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

section Defs
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ Qb)

abbrev R₀ : Subring LQ :=
  modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)

abbrev ev (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) : ↥(R₀ q A red a K) :=
  ⟨modularEval (1 * q) (coeffSubring A K) p,
    modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) p⟩

def evHom : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(R₀ q A red a K) :=
  (modularEval (1 * q) (coeffSubring A K)).codRestrict (R₀ q A red a K)
    (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))

theorem evHom_apply (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) : evHom q A red a K p = ev q A red a K p := rfl

def constHom : ↥(coeffSubring A K) →+* ↥(R₀ q A red a K) :=
  (evHom q A red a K).comp MvPolynomial.C

theorem constHom_apply (c : ↥(coeffSubring A K)) :
    constHom q A red a K c = ev q A red a K (MvPolynomial.C c) := rfl

end Defs

section RedLemmas
variable {A : ValuationSubring Qb} {k : Type*} [Field k]

theorem mem_coeffSubring_iff' (K : IntermediateField ℚ Qb) {x : Qb} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := Iff.rfl

theorem red_eq_zero_of_mem_maximalIdeal (red : A →+* k) (q : ℕ) [Fact q.Prime] [CharP k q] (τ : A) (hτ : τ ∈ IsLocalRing.maximalIdeal A) : red τ = 0 := by
  have hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hA : A.LiesOverPrime q := by
    rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff]
    have hnu : ¬ IsUnit (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) := by
      intro hu
      have h1 := hu.map red
      have h0 : red ⟨(q : AlgebraicClosure ℚ), hq⟩ = 0 := by
        have : (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) = (q : A) := Subtype.ext (by push_cast; rfl)
        rw [this, map_natCast, CharP.cast_eq_zero]
      rw [h0] at h1
      exact not_isUnit_zero h1
    exact (ValuationSubring.valuation_lt_one_iff A ⟨(q : AlgebraicClosure ℚ), hq⟩).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  exact ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A q hA red τ
    ((ValuationSubring.valuation_lt_one_iff A τ).mp hτ)

theorem isUnit_coeffSubring_iff (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    (c : ↥(coeffSubring A K)) : IsUnit c ↔ redRestrict red K c ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ hc
    have h1 : redRestrict red K ((u * u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) = 1 := by
      rw [mul_inv_cancel, Units.val_one, map_one]
    rw [Units.val_mul, map_mul, hc, zero_mul] at h1
    exact zero_ne_one h1
  · intro hc
    have hcA : (c : Qb) ∈ A := ((mem_coeffSubring_iff' (A := A) K).mp c.2).1
    have hcK : (c : Qb) ∈ K := ((mem_coeffSubring_iff' (A := A) K).mp c.2).2
    have hcm : (⟨(c : Qb), hcA⟩ : A) ∉ IsLocalRing.maximalIdeal A := fun hm =>
      hc (red_eq_zero_of_mem_maximalIdeal red q _ hm)
    have hu : IsUnit (⟨(c : Qb), hcA⟩ : A) := by
      by_contra h; exact hcm ((IsLocalRing.mem_maximalIdeal _).mpr h)
    obtain ⟨u, hu⟩ := hu
    have hmul : (((u⁻¹ : Aˣ) : A) : Qb) * (c : Qb) = 1 := by
      have h := congrArg (fun z : A => (z : Qb)) u.inv_mul
      rw [hu] at h
      simpa using h
    have hinv : (c : Qb)⁻¹ = (((u⁻¹ : Aˣ) : A) : Qb) := inv_eq_of_mul_eq_one_left hmul
    have hinvmem : (c : Qb)⁻¹ ∈ coeffSubring A K :=
      (mem_coeffSubring_iff' (A := A) K).mpr ⟨hinv ▸ ((u⁻¹ : Aˣ) : A).2, K.inv_mem hcK⟩
    have hc0 : (c : Qb) ≠ 0 := by
      rintro h0
      apply hc
      have : c = 0 := Subtype.ext h0
      rw [this, map_zero]
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvmem⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩

theorem stepA_dvr (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    [FiniteDimensional ℚ K] : IsDiscreteValuationRing ↥(coeffSubring A K) := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · exfalso
    have hqK : ((q : ℕ) : Qb)⁻¹ ∈ coeffSubring A K := by
      rw [h]; exact (K.inv_mem (natCast_mem K q) : ((q : ℕ) : Qb)⁻¹ ∈ K)
    have hu : IsUnit (((q : ℕ) : ↥(coeffSubring A K))) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hqK⟩, Subtype.ext (by
        push_cast
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))⟩
    have := (isUnit_coeffSubring_iff red K q _).mp hu
    apply this
    rw [map_natCast, CharP.cast_eq_zero]
  · exact h

theorem stepA_uniformizer (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(coeffSubring A K), Irreducible ϖ ∧ (∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) ∧
      ∃ (e : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ e ∧ IsUnit ε ∧ ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ e * ε := by
  classical
  haveI := stepA_dvr red K q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
  have hker : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d := by
    intro c
    have h1 : redRestrict red K c = 0 ↔ ¬ IsUnit c := by
      rw [isUnit_coeffSubring_iff red K q c, not_not]
    rw [h1, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact Iff.rfl
  refine ⟨ϖ, hϖ, hker, ?_⟩
  have hq0 : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
    intro h
    have := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) h
    push_cast at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ
  refine ⟨n, u, ?_, u.isUnit, by rw [hn, mul_comm]⟩
  by_contra hlt
  have hn0 : n = 0 := by omega
  rw [hn0, pow_zero, mul_one] at hn
  have hu : IsUnit ((q : ℕ) : ↥(coeffSubring A K)) := hn ▸ u.isUnit
  exact ((isUnit_coeffSubring_iff red K q _).mp hu) (by rw [map_natCast, CharP.cast_eq_zero])

end RedLemmas

section Main
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]
variable (red : A →+* k) (a : k) (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K]

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in

theorem isPrincipalIdealRing_of_maximalIdeal_eq_span_singleton {S : Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [IsLocalRing S] (g : S) (hg : IsLocalRing.maximalIdeal S = Ideal.span {g}) : IsPrincipalIdealRing S := by
  classical
  by_cases hF : IsField S
  · refine ⟨fun I => ?_⟩
    have hbot : IsLocalRing.maximalIdeal S = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
    by_cases hI : I = ⊤
    · exact ⟨⟨1, by rw [hI, Ideal.submodule_span_eq, Ideal.span_singleton_one]⟩⟩
    · have hIbot : I = ⊥ := le_bot_iff.mp ((IsLocalRing.le_maximalIdeal hI).trans hbot.le)
      exact ⟨⟨0, by rw [hIbot, Ideal.submodule_span_eq, eq_comm, Ideal.span_singleton_eq_bot]⟩⟩
  · have hprinc : (IsLocalRing.maximalIdeal S).IsPrincipal := ⟨⟨g, by rw [hg, Ideal.submodule_span_eq]⟩⟩
    haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hF).out 0 4).mpr hprinc
    infer_instance

theorem mainIC (ha : a ^ (q ^ 2) ≠ a) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) :
    IsIntegrallyClosed ↥(R₀ q A red a K) := by
  classical
  obtain ⟨ϖ, -, hϖ, -⟩ := stepA_uniformizer red K q
  obtain ⟨hnoeth, hloc, -, -⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI := hnoeth
  haveI := hloc
  obtain ⟨hprime, hmax⟩ :=
    ModularCurve.isPrime_span_uniformizer_and_maximalIdeal_modularLocalizedAtPoint_eq_of_pow_sq_ne red a ha K x hx ϖ hϖ
  have hmax' := @hmax hloc
  set cϖ : ↥(R₀ q A red a K) := ev q A red a K (MvPolynomial.C ϖ) with hcϖ
  set cJx : ↥(R₀ q A red a K) := ev q A red a K (MvPolynomial.X 0 - MvPolynomial.C x) with hcJx
  change (Ideal.span {cϖ}).IsPrime at hprime
  change IsLocalRing.maximalIdeal ↥(R₀ q A red a K) = Ideal.span {cϖ, cJx} at hmax'
  have hϖm : cϖ ∈ IsLocalRing.maximalIdeal ↥(R₀ q A red a K) := by
    rw [hmax']; exact Ideal.subset_span (Set.mem_insert _ _)
  haveI hQdom : IsDomain (↥(R₀ q A red a K) ⧸ Ideal.span {cϖ}) := (Ideal.Quotient.isDomain_iff_prime _).mpr hprime
  haveI hQloc : IsLocalRing (↥(R₀ q A red a K) ⧸ Ideal.span {cϖ}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {cϖ})) Ideal.Quotient.mk_surjective

  have h1 : Ideal.map (Ideal.Quotient.mk (Ideal.span {cϖ})) (IsLocalRing.maximalIdeal ↥(R₀ q A red a K))
      = Ideal.span {Ideal.Quotient.mk (Ideal.span {cϖ}) cJx} := by
    rw [hmax', Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton cϖ))]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ (rfl | rfl)
      · exact zero_mem _
      · exact Ideal.subset_span (Set.mem_singleton _)
    · exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hQmax : IsLocalRing.maximalIdeal (↥(R₀ q A red a K) ⧸ Ideal.span {cϖ})
      = Ideal.span {Ideal.Quotient.mk (Ideal.span {cϖ}) cJx} := by
    rw [← h1]
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {cϖ})) Ideal.Quotient.mk_surjective
        (IsLocalRing.maximalIdeal.isMaximal ↥(R₀ q A red a K)) with htop | hM
    · exfalso
      have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk (Ideal.span {cϖ}))) htop
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_top, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hϖm)] at h2
      exact (IsLocalRing.maximalIdeal.isMaximal ↥(R₀ q A red a K)).ne_top h2
    · exact (IsLocalRing.eq_maximalIdeal hM).symm
  haveI : IsPrincipalIdealRing (↥(R₀ q A red a K) ⧸ Ideal.span {cϖ}) :=
    isPrincipalIdealRing_of_maximalIdeal_eq_span_singleton _ hQmax
  exact IsLocalRing.isIntegrallyClosed_of_isPrincipalIdealRing_quotient cϖ

end Main
end RegRIC
end ModularCurve

open ModularCurve.RegRIC in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] [DecidableEq k]
    (red : A →+* k) (a : k) (ha : a ^ (q ^ 2) ≠ a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) :
    IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
  ModularCurve.RegRIC.mainIC red a K ha x hx

end
