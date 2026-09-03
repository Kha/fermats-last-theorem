import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PDivisibleGroup_CartierDuality
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one
attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} (H H' : PDivisibleGroup O p h) (D : H.CartierDuality H')
    (v : ℕ)

    (Mt : Type) [CommRing Mt] [HopfAlgebra O Mt] [Coalgebra.IsCocomm O Mt] [Module.Free O Mt] [Module.Finite O Mt]
    [Algebra.Etale O (CartierDual O Mt)]
    (π : H.level v →ₐc[O] Mt)
    (f : H.Point (AlgebraicClosure ℚ) v) (g : Mt →ₐ[O] AlgebraicClosure ℚ)
    (hfg : PDivisibleGroup.Point.toAlgHom f = g.comp (π : H.level v →ₐ[O] Mt))

    (ψ : H'.Point (AlgebraicClosure ℚ) v)
    (hψ : ∀ a : H'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
      algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :
    D.pair (AlgebraicClosure ℚ) v f ψ = 1 := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one.solution
