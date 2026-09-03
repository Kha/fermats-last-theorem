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
import P2M.Sol.S_GaloisRepAdic_IsEquiv_ordinaryCondition

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem GaloisRepAdic.IsEquiv.ordinaryCondition
    {𝒪 : Type} [CommRing 𝒪] {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (p : ℕ) (S : Finset ℕ) (ρ ρ' : GaloisRepAdic A) (h : ρ.IsEquiv ρ') :
    GaloisRep.ordinaryCondition 𝒪 p S ρ → GaloisRep.ordinaryCondition 𝒪 p S ρ' := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_IsEquiv_ordinaryCondition.solution
