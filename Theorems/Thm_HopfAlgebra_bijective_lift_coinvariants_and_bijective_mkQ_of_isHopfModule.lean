import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_bijective_lift_coinvariants_and_bijective_mkQ_of_isHopfModule

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.bijective_lift_coinvariants_and_bijective_mkQ_of_isHopfModule
    {R : Type} [CommRing R] {L : Type} [CommRing L] [HopfAlgebra R L]
    {M : Type} [AddCommGroup M] [Module R M] [Module L M] [IsScalarTower R L M]
    (ρ : M →ₗ[R] M ⊗[R] L)
    (hcoassoc : (TensorProduct.assoc R M L L).toLinearMap ∘ₗ ρ.rTensor L ∘ₗ ρ =
      (Coalgebra.comul (R := R) (A := L)).lTensor M ∘ₗ ρ)
    (hcounit : (Coalgebra.counit (R := R) (A := L)).lTensor M ∘ₗ ρ = (TensorProduct.mk R M R).flip 1)
    (hmod : ∀ (c : L) (m : M), ρ (c • m) =
      TensorProduct.map (TensorProduct.lift ((Algebra.lsmul R R M : L →ₐ[R] Module.End R M).toLinearMap))
          (LinearMap.mul' R L)
        (TensorProduct.tensorTensorTensorComm R L L M L (Coalgebra.comul (R := R) c ⊗ₜ[R] ρ m))) :
    let Mco : Submodule R M := LinearMap.ker (ρ - (TensorProduct.mk R M L).flip (1 : L))
    Function.Bijective
        (TensorProduct.lift
          (((Algebra.lsmul R R M : L →ₐ[R] Module.End R M).toLinearMap.flip) ∘ₗ Mco.subtype) :
          Mco ⊗[R] L → M) ∧
      Function.Bijective (fun m : Mco =>
        (Submodule.Quotient.mk (m : M) :
          M ⧸ ((RingHom.ker (Bialgebra.counitAlgHom R L)) • (⊤ : Submodule L M)))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_bijective_lift_coinvariants_and_bijective_mkQ_of_isHopfModule.solution
