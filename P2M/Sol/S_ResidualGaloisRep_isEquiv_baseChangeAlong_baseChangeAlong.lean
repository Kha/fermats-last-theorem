import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_isEquiv_baseChangeAlong_baseChangeAlong

set_option autoImplicit false
open scoped TensorProduct

namespace BCBCRProof

theorem aux
    {k k' k'' : Type} [Field k] [Field k'] [Field k''] [Algebra k k'] [Algebra k' k''] [Algebra k k'']
    [IsScalarTower k k' k''] (ρ : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : k'' ⊗[k'] (k' ⊗[k] ρ.V)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V
        (LinearMap.baseChange k'' (LinearMap.baseChange k' (ρ.ρ σ)) x) =
      LinearMap.baseChange k'' (ρ.ρ σ) (TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul b v =>
      simp only [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

end BCBCRProof

theorem solution
    {k k' k'' : Type} [Field k] [Field k'] [Field k''] (ψ : k →+* k') (ψ' : k' →+* k'') (ρ : ResidualGaloisRep k) :
    ((ρ.baseChangeAlong ψ).baseChangeAlong ψ').IsEquiv (ρ.baseChangeAlong (ψ'.comp ψ)) := by
  classical
  letI : Algebra k k' := ψ.toAlgebra
  letI : Algebra k' k'' := ψ'.toAlgebra
  letI : Algebra k k'' := (ψ'.comp ψ).toAlgebra
  haveI : IsScalarTower k k' k'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨{ toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V
            map_apply := ?_ }⟩
  intro σ x
  exact BCBCRProof.aux ρ σ x
