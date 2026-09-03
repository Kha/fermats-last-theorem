import Mathlib
import Theorems.Thm_HopfAlgebra_exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
import Theorems.Thm_HopfAlgebra_bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
import P2M.Util
namespace P2MW.S_HopfAlgebra_existsUnique_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff

set_option autoImplicit false

universe u v

open IsLocalRing
open scoped TensorProduct

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {H : Type u} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
    (M : Type v) [AddCommGroup M] [Finite M]
    (ψ₀ : ResidueField R ⊗[R] H →ₐc[ResidueField R] AddMonoidAlgebra (ResidueField R) M) :
    ∃! ψ : H →ₐc[R] AddMonoidAlgebra R M,
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp (ψ : H →ₐ[R] AddMonoidAlgebra R M) =
        ((ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] AddMonoidAlgebra (ResidueField R) M).restrictScalars R).comp
          Algebra.TensorProduct.includeRight := by
  obtain ⟨ψ, hψ⟩ := HopfAlgebra.exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing M ψ₀
  exact ⟨ψ, hψ, fun ψ' h' =>
    HopfAlgebra.bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq M ψ' ψ (h'.trans hψ.symm)⟩
