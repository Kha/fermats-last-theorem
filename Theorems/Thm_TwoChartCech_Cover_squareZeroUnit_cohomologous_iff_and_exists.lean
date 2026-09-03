import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import P2M.Util
import P2M.Sol.S_TwoChartCech_Cover_squareZeroUnit_cohomologous_iff_and_exists

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem TwoChartCech.Cover.squareZeroUnit_cohomologous_iff_and_exists
    {K : Type u} [Field K] (𝒰 : TwoChartCech.Cover.{u, u} K)
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] :
    (∀ t t' : (TrivSqZeroExt K V ⊗[K] 𝒰.A01)ˣ,
      Algebra.TensorProduct.lift ((Algebra.ofId K 𝒰.A01).comp (TrivSqZeroExt.fstHom K K V)) (AlgHom.id K 𝒰.A01)
          (fun _ _ => Commute.all _ _) (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) = 1 →
      Algebra.TensorProduct.lift ((Algebra.ofId K 𝒰.A01).comp (TrivSqZeroExt.fstHom K K V)) (AlgHom.id K 𝒰.A01)
          (fun _ _ => Commute.all _ _) (t' : TrivSqZeroExt K V ⊗[K] 𝒰.A01) = 1 →
      ((∃ (a0 : (TrivSqZeroExt K V ⊗[K] 𝒰.A0)ˣ) (a1 : (TrivSqZeroExt K V ⊗[K] 𝒰.A1)ˣ),
          (t' : TrivSqZeroExt K V ⊗[K] 𝒰.A01) =
            Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) 𝒰.ρ0 (a0 : TrivSqZeroExt K V ⊗[K] 𝒰.A0) *
              (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) *
            Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) 𝒰.ρ1
              ((↑a1⁻¹ : (TrivSqZeroExt K V ⊗[K] 𝒰.A1)ˣ) : TrivSqZeroExt K V ⊗[K] 𝒰.A1)) ↔
        (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V
            ((TensorProduct.comm K V 𝒰.A01).toLinearMap
              (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01))) =
          (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V
            ((TensorProduct.comm K V 𝒰.A01).toLinearMap
              (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id (t' : TrivSqZeroExt K V ⊗[K] 𝒰.A01))))) ∧
    (∀ y : 𝒰.structureSheaf.H1 ⊗[K] V, ∃ t : (TrivSqZeroExt K V ⊗[K] 𝒰.A01)ˣ,
      Algebra.TensorProduct.lift ((Algebra.ofId K 𝒰.A01).comp (TrivSqZeroExt.fstHom K K V)) (AlgHom.id K 𝒰.A01)
          (fun _ _ => Commute.all _ _) (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) = 1 ∧
      (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V
          ((TensorProduct.comm K V 𝒰.A01).toLinearMap
            (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01))) = y) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Cover_squareZeroUnit_cohomologous_iff_and_exists.solution
