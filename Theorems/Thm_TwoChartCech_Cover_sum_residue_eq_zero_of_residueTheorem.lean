import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import P2M.Util
import P2M.Sol.S_TwoChartCech_Cover_sum_residue_eq_zero_of_residueTheorem

set_option autoImplicit false

universe u w

theorem TwoChartCech.Cover.sum_residue_eq_zero_of_residueTheorem
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
    ∑ i, (Λ i).residue η = 0 := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Cover_sum_residue_eq_zero_of_residueTheorem.solution
