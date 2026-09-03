import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_CartierDual_isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange
attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff

set_option autoImplicit false
open scoped TensorProduct in

theorem CartierDual.isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (k₀ : Type) [Field k₀] [CharP k₀ p] [Algebra (GaloisRep.ratLocalizedAt p) k₀] :
    (IsLocalRing H → IsLocalRing (k₀ ⊗[GaloisRep.ratLocalizedAt p] H)) ∧
      (IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H) →
        IsLocalRing (CartierDual k₀ (k₀ ⊗[GaloisRep.ratLocalizedAt p] H))) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange.solution
