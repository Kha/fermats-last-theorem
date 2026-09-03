import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

set_option autoImplicit false
open scoped TensorProduct

theorem GaloisRep.bijective_lift_pi_algHom_of_finiteFlatHopf
    (q : ℕ) [Fact q.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H] :
    Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom (GaloisRep.ratLocalizedAt q) _
          fun ν : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) => (WithConv.ofConv ν : H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[GaloisRep.ratLocalizedAt q] H →ₐ[AlgebraicClosure ℚ] (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf.solution
