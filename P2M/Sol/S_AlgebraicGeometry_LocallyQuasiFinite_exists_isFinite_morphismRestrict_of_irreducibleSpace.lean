import Mathlib
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_exists_isFinite_morphismRestrict_of_irreducibleSpace

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated f] [QuasiCompact f] [IrreducibleSpace Y] :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ IsFinite (f ∣_ U) := by
  classical

  let η : Y := genericPoint Y
  obtain ⟨V₀, hV₀, hηV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top η)
  let V : Y.Opens := V₀
  have hV : IsAffineOpen V := hV₀
  have hηV : η ∈ V := hηV
  let e := hV.isoSpec
  let g : (f ⁻¹ᵁ V).toScheme ⟶ Spec (CommRingCat.of Γ(Y, V)) := (f ∣_ V) ≫ e.hom

  let p : PrimeSpectrum Γ(Y, V) := e.hom.base ⟨η, hηV⟩
  have hpmin : p.asIdeal ∈ minimalPrimes Γ(Y, V) := by
    rw [minimalPrimes_eq_minimals]
    refine ⟨p.isPrime, fun q hq hqp => ?_⟩

    let y : V := e.inv.base ⟨q, hq⟩
    have h1 : (⟨η, hηV⟩ : V) ⤳ y := by
      rw [← Topology.IsInducing.subtypeVal.specializes_iff]
      exact genericPoint_specializes _
    have h2 : p ⤳ e.hom.base y := h1.map e.hom.continuous
    have h3 : e.hom.base y = ⟨q, hq⟩ := by
      show (e.inv ≫ e.hom).base ⟨q, hq⟩ = _
      rw [e.inv_hom_id]; rfl
    rw [h3, ← PrimeSpectrum.le_iff_specializes] at h2
    exact h2
  haveI : IsSeparated g := inferInstance
  obtain ⟨r, hrp, hfin⟩ :=
    AlgebraicGeometry.LocallyQuasiFinite.exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes
      g p.asIdeal hpmin

  let W : V.toScheme.Opens := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
  refine ⟨V.ι ''ᵁ W, ⟨η, ?_⟩, ?_⟩
  · refine ⟨⟨η, hηV⟩, ?_, rfl⟩
    show p ∈ PrimeSpectrum.basicOpen r
    exact hrp
  ·
    have h1 : IsFinite ((f ∣_ V) ∣_ W) := by
      have hc : g ∣_ PrimeSpectrum.basicOpen r = ((f ∣_ V) ∣_ W) ≫ (e.hom ∣_ PrimeSpectrum.basicOpen r) :=
        morphismRestrict_comp _ _ _
      rw [hc] at hfin
      exact (MorphismProperty.cancel_right_of_respectsIso @IsFinite ((f ∣_ V) ∣_ W)
        (e.hom ∣_ PrimeSpectrum.basicOpen r)).mp hfin
    exact ((MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict f V W)).mp h1)
