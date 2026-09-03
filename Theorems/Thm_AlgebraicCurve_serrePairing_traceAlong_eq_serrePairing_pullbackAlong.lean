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
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_pullbackAlong

open KaehlerDifferential
namespace AlgebraicCurve
theorem serrePairing_traceAlong_eq_serrePairing_pullbackAlong
    {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [IsCurveOver K F']
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) (hRT' : ResidueTheorem K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hsep : SeparableAlong K φ)
    (hfib : FibreResidueIdentityAlong φ hφ)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (ω' : ↥(regularDifferentials K F'))
    (hω : Differential.traceAlong φ (ω' : Ω[F'⁄K]) ∈ regularDifferentials K F)
    (x : cechH1 S₀ S₁ (0 : Divisor K F)) :
    serrePairing hRT hcover ⟨Differential.traceAlong φ (ω' : Ω[F'⁄K]), hω⟩ x
      = serrePairing hRT' (preimage_restrictAlong_union_eq_univ φ hφ hcover) ω'
          (cechH1.pullbackAlong φ hφ S₀ S₁ x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_pullbackAlong.solution
end AlgebraicCurve
