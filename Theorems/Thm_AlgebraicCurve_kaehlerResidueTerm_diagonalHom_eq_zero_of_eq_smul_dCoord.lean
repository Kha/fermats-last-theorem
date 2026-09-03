import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
    {v : Place K F} [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω : Ω[F⁄K]} {f : F} (hf : f ∈ v.toValuationSubring) (hω : ω = f • v.dCoord)
    {g : F} (hg : g ∈ v.toValuationSubring) :
    kaehlerResidueTerm ω (diagonalHom K F g) v = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord.solution
