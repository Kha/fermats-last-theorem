import Mathlib
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_PDivisibleGroup_CartierDuality
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_IsCartierDual_baseChange
attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff

set_option autoImplicit false

theorem PDivisibleGroup.IsCartierDual.baseChange
    {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (hGG' : G.IsCartierDual G')
    (S : Type) [CommRing S] [Algebra R S] [Nontrivial S] :
    (G.baseChange S).IsCartierDual (G'.baseChange S) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_IsCartierDual_baseChange.solution
