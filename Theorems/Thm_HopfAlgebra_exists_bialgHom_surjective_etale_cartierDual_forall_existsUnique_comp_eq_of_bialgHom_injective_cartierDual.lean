import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual
attribute [-instance] CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual
    (R : Type u) [CommRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Free R H]

    (E : Type (max u v)) [CommRing E] [HopfAlgebra R E] [Coalgebra.IsCocomm R E]
    [Module.Free R E] [Module.Finite R E] (ι : E →ₐc[R] CartierDual R H)
    (hι : Function.Injective ι)
    (hE : Algebra.Etale R E)
    (huniv : ∀ (E' : Type (max u v)) [CommRing E'] [HopfAlgebra R E'] [Coalgebra.IsCocomm R E']
        [Module.Free R E'] [Module.Finite R E'] [Algebra.Etale R E']
        (f : E' →ₐc[R] CartierDual R H), ∃! g : E' →ₐc[R] E, ι.comp g = f)
    (hsplit : Module.Free R (CartierDual R H ⧸
      (LinearMap.range (ι : E →ₐ[R] CartierDual R H).toLinearMap : Submodule R (CartierDual R H))))
    (hbc : ∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
        IsLocalHom (algebraMap R R') →
        Algebra.Etale R' (R' ⊗[R] E) ∧
        ∀ (E' : Type (max u v)) [CommRing E'] [HopfAlgebra R' E'] [Coalgebra.IsCocomm R' E']
          [Module.Free R' E'] [Module.Finite R' E'] [Algebra.Etale R' E']
          (f : E' →ₐc[R'] R' ⊗[R] CartierDual R H),
            ∃! g : E' →ₐc[R'] R' ⊗[R] E,
              (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι).comp g = f) :
    ∃ (M : Type v) (_ : CommRing M) (_ : HopfAlgebra R M) (_ : Coalgebra.IsCocomm R M)
      (_ : Module.Free R M) (_ : Module.Finite R M) (π : H →ₐc[R] M),
      Function.Surjective π ∧

      Algebra.Etale R (CartierDual R M) ∧

      (∀ (M' : Type v) [CommRing M'] [HopfAlgebra R M'] [Coalgebra.IsCocomm R M']
          [Module.Free R M'] [Module.Finite R M'] [Algebra.Etale R (CartierDual R M')]
          (f : H →ₐc[R] M'), ∃! g : M →ₐc[R] M', g.comp π = f) ∧

      (∀ φ : H →ₐc[R] H, ∃! ψ : M →ₐc[R] M, ψ.comp π = π.comp φ) ∧

      (∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
          IsLocalHom (algebraMap R R') →
          Algebra.Etale R' (CartierDual R' (R' ⊗[R] M)) ∧
          ∀ (N : Type v) [CommRing N] [HopfAlgebra R' N] [Coalgebra.IsCocomm R' N]
            [Module.Free R' N] [Module.Finite R' N] [Algebra.Etale R' (CartierDual R' N)]
            (f : R' ⊗[R] H →ₐc[R'] N),
              ∃! g : R' ⊗[R] M →ₐc[R'] N,
                g.comp (Bialgebra.TensorProduct.map (BialgHom.id R' R') π) = f) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual.solution
