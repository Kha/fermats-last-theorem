import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import P2M.Util
import P2M.Sol.S_GaloisRep_DeformationRingData_surjective_of_isEquiv_baseChangeAlong_of_isOfType_quotient

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem GaloisRep.DeformationRingData.surjective_of_isEquiv_baseChangeAlong_of_isOfType_quotient
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hB : ∀ [IsLocalRing (D'.R ⧸ RingHom.ker (θ : D'.R →+* D₀.R))]
        (hmk : IsLocalHom (Ideal.Quotient.mk (RingHom.ker (θ : D'.R →+* D₀.R)))),
        𝒟₀ (D'.ρ.baseChangeAlong (Ideal.Quotient.mk (RingHom.ker (θ : D'.R →+* D₀.R))) hmk)) :
    Function.Surjective θ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_DeformationRingData_surjective_of_isEquiv_baseChangeAlong_of_isOfType_quotient.solution
