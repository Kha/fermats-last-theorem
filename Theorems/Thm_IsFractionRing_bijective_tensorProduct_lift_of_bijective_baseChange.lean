import Mathlib
import P2M.Util
import P2M.Sol.S_IsFractionRing_bijective_tensorProduct_lift_of_bijective_baseChange

set_option autoImplicit false

open scoped TensorProduct

theorem IsFractionRing.bijective_tensorProduct_lift_of_bijective_baseChange
    {R S Rhat T K₁ K E F : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [CommRing Rhat] [IsDomain Rhat]
    [CommRing T] [IsDomain T] [Field K₁] [Field K] [Field E] [Field F]

    [Algebra R S] [Module.Finite R S] [NoZeroSMulDivisors R S]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra S K] [IsFractionRing S K]
    [Algebra R K] [Algebra K₁ K] [IsScalarTower R S K] [IsScalarTower R K₁ K]

    [Algebra R Rhat] [Algebra Rhat E] [IsFractionRing Rhat E]
    [Algebra R E] [Algebra K₁ E] [IsScalarTower R Rhat E] [IsScalarTower R K₁ E]

    [Algebra Rhat T] [Algebra S T] [Algebra R T] [IsScalarTower R Rhat T] [IsScalarTower R S T]
    (hT : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId Rhat T) (IsScalarTower.toAlgHom R S T)
        (fun _ _ => Commute.all _ _) : Rhat ⊗[R] S →ₐ[Rhat] T))
    [Algebra T F] [IsFractionRing T F]

    [Algebra E F] [Algebra Rhat F] [IsScalarTower Rhat E F] [IsScalarTower Rhat T F]
    [Algebra K F] [Algebra S F] [IsScalarTower S K F] [IsScalarTower S T F]
    [Algebra K₁ F] [IsScalarTower K₁ E F] [IsScalarTower K₁ K F] :
    Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId E F) (IsScalarTower.toAlgHom K₁ K F)
        (fun _ _ => Commute.all _ _) : E ⊗[K₁] K →ₐ[E] F) := by p2m_exact_reverting @_root_.P2MW.S_IsFractionRing_bijective_tensorProduct_lift_of_bijective_baseChange.solution
