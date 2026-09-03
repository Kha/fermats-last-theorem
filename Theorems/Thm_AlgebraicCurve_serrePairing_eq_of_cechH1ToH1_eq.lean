import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_SerrePairing
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_serrePairing_eq_of_cechH1ToH1_eq

open KaehlerDifferential
namespace AlgebraicCurve
theorem serrePairing_eq_of_cechH1ToH1_eq {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalLocalResidueKStar K F] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalDivisor (K := K) (F := F)] [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) {S₀ S₁ T₀ T₁ : Set (Place K F)}
    (hS : S₀ ∪ S₁ = Set.univ) (hT : T₀ ∪ T₁ = Set.univ)
    (ω : ↥(regularDifferentials K F)) (x : cechH1 S₀ S₁ (0 : Divisor K F)) (y : cechH1 T₀ T₁ (0 : Divisor K F))
    (h : cechH1ToH1 hS 0 x = cechH1ToH1 hT 0 y) :
    serrePairing hRT hS ω x = serrePairing hRT hT ω y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_serrePairing_eq_of_cechH1ToH1_eq.solution
end AlgebraicCurve
