import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import P2M.Util
namespace P2MW.S_TwoChartCech_Cover_sum_residue_eq_zero_of_residueTheorem

set_option autoImplicit false

universe u w

theorem solution
    {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar k F]
    [∀ v : AlgebraicCurve.Place k F, v.DCoordGenerates] [Nontrivial Ω[F⁄k]]
    [AlgebraicCurve.HasCanonicalDivisor (K := k) (F := F)] [AlgebraicCurve.HasPrincipalDivisors k F]
    (hRT : AlgebraicCurve.ResidueTheorem k F)
    (𝒰 : TwoChartCech.Cover.{u, u} k) {ι : Type w} [Fintype ι] (Λ : ι → 𝒰.LaurentChart)
    (Φ : Ω[𝒰.A01⁄k] →ₗ[k] Ω[F⁄k]) (p : ι ↪ AlgebraicCurve.Place k F)
    (hres : ∀ (i : ι) (η : Ω[𝒰.A01⁄k]),
      (Λ i).residue η = AlgebraicCurve.kaehlerResidueTerm (Φ η) (AlgebraicCurve.diagonalHom k F 1) (p i))
    (η : Ω[𝒰.A01⁄k])
    (hreg : ∀ v : AlgebraicCurve.Place k F, v ∉ Set.range p →
      AlgebraicCurve.kaehlerResidueTerm (Φ η) (AlgebraicCurve.diagonalHom k F 1) v = 0) :
    ∑ i, (Λ i).residue η = 0 := by
  classical
  simp_rw [hres]
  rcases eq_or_ne (Φ η) 0 with hω | hω
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [hω]
    exact AlgebraicCurve.kaehlerResidueTerm_eq_zero_of_ord_nonneg
      (Or.inl (by rw [AlgebraicCurve.Place.differentialCoeff_zero, mul_zero]))
  · have h : ∑ᶠ v, AlgebraicCurve.kaehlerResidueTerm (Φ η) (AlgebraicCurve.diagonalHom k F 1) v = 0 := by
      have := hRT hω (1 : F)
      rwa [AlgebraicCurve.weilOfKaehler_apply] at this
    have hsupp : Function.support
        (fun v => AlgebraicCurve.kaehlerResidueTerm (Φ η) (AlgebraicCurve.diagonalHom k F 1) v) ⊆
          ((Finset.univ.map p : Finset (AlgebraicCurve.Place k F)) : Set (AlgebraicCurve.Place k F)) := by
      intro v hv
      rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
      by_contra hv'
      exact hv (hreg v hv')
    rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map] at h
    exact h
