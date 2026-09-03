import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_signTwist_comul_mul_padicInt
attribute [-instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

open scoped TensorProduct
open scoped TensorProduct in
theorem HopfAlgebra.signTwist_comul_mul_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    let Δ' : H →ₗ[ℤ_[p]] (H ⊗[ℤ_[p]] H) :=
      Coalgebra.comul + (Ring.inverse d₀ - 1) • ((TensorProduct.map Pm Pm).comp Coalgebra.comul)
    let μ'ₗ : (H ⊗[ℤ_[p]] H) →ₗ[ℤ_[p]] H :=
      LinearMap.mul' ℤ_[p] H + (d₀ - 1) • ((LinearMap.mul' ℤ_[p] H).comp (TensorProduct.map Pm Pm))
    ∀ a b : H, Δ' (μ'ₗ (a ⊗ₜ b))
      = (TensorProduct.map μ'ₗ μ'ₗ)
          ((TensorProduct.tensorTensorTensorComm ℤ_[p] H H H H) (Δ' a ⊗ₜ Δ' b)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_signTwist_comul_mul_padicInt.solution
