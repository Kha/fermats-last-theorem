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
import Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_isEquiv
import P2M.Util
namespace P2MW.S_GaloisRepAdic_IsEquiv_isUnipotentOnInertiaAt

set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (q : ℕ) (ρ ρ' : GaloisRepAdic A) (h : ρ.IsEquiv ρ') :
    ρ.IsUnipotentOnInertiaAt q → ρ'.IsUnipotentOnInertiaAt q :=
  fun h' => GaloisRepAdic.isUnipotentOnInertiaAt_of_isEquiv h h'
