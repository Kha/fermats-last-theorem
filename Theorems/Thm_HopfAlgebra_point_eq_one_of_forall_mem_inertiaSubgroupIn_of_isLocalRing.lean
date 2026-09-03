import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_of_isLocalRing
attribute [-instance] AlgebraicClosure.Rat.isGalois instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem HopfAlgebra.point_eq_one_of_forall_mem_inertiaSubgroupIn_of_isLocalRing
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H] [IsLocalRing H]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))
    (hf : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g = f) :
    f = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_of_isLocalRing.solution
