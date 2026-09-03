import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue
import P2M.Util
namespace P2MW.S_AlgebraicCurve_kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
    {v : Place K F} [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω : Ω[F⁄K]} {f : F} (hf : f ∈ v.toValuationSubring) (hω : ω = f • v.dCoord)
    {g : F} (hg : g ∈ v.toValuationSubring) :
    kaehlerResidueTerm ω (diagonalHom K F g) v = 0 := by
  unfold kaehlerResidueTerm
  rw [diagonalHom_apply, v.differentialCoeff_unique hω, v.localResidue_of_mem (mul_mem hg hf), map_zero]
