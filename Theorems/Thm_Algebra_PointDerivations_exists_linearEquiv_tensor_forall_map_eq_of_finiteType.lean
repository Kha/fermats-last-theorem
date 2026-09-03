import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_Algebra_PointDerivations_exists_linearEquiv_tensor_forall_map_eq_of_finiteType

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Scheme.TwoAffineOpenCover

universe u

theorem Algebra.PointDerivations.exists_linearEquiv_tensor_forall_map_eq_of_finiteType
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (ev : A →+* k) (hev : ev.comp (algebraMap k A) = RingHom.id k) :
    ∃ Ψ : ∀ (M : Type u) [AddCommGroup M] [Module k M],
        ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k] (↥(Algebra.PointDerivations k A ev k) ⊗[k] M),
      (∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
          (δ : ↥(Algebra.PointDerivations k A ev M)),
        Ψ M' (Algebra.PointDerivations.map ev g δ) =
          LinearMap.lTensor (↥(Algebra.PointDerivations k A ev k)) g (Ψ M δ)) ∧
      (∀ δ : ↥(Algebra.PointDerivations k A ev k), Ψ k δ = δ ⊗ₜ[k] (1 : k)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_PointDerivations_exists_linearEquiv_tensor_forall_map_eq_of_finiteType.solution
