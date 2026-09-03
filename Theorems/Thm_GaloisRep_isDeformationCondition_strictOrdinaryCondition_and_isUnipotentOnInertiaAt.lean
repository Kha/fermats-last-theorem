import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_StrictOrdinary
import P2M.Util
import P2M.Sol.S_GaloisRep_isDeformationCondition_strictOrdinaryCondition_and_isUnipotentOnInertiaAt
attribute [-instance] GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra
attribute [-simp] GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec

set_option autoImplicit false
theorem GaloisRep.isDeformationCondition_strictOrdinaryCondition_and_isUnipotentOnInertiaAt
    (𝒪 : Type) [CommRing 𝒪] {p : ℕ} {S U : Finset ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GaloisRep.IsDeformationCondition 𝒪
      (fun _A _ _ _ ρ => GaloisRep.strictOrdinaryCondition 𝒪 p S ρ ∧
        ∀ q ∈ U, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_isDeformationCondition_strictOrdinaryCondition_and_isUnipotentOnInertiaAt.solution
