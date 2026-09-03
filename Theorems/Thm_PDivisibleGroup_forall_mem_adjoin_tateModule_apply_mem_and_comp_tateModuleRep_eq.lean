import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_forall_mem_adjoin_tateModule_apply_mem_and_comp_tateModuleRep_eq

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.forall_mem_adjoin_tateModule_apply_mem_and_comp_tateModuleRep_eq
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    {h : ℕ} (H : PDivisibleGroup O p h)
    (u : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (U : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (hU : ∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ)
      (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
        (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
      ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom f).comp (u w : H.level w →ₐ[O] H.level w)))))
    (S : Submodule ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (hS : ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ S ↔
        ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :
    ∀ V ∈ Algebra.adjoin ℤ_[p] ({U} : Set (Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))),
      (∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ S → V y ∈ S) ∧
      (∀ τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ,
        H.tateModuleRep (AlgebraicClosure ℚ) τ' ∘ₗ V = V ∘ₗ H.tateModuleRep (AlgebraicClosure ℚ) τ') := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_forall_mem_adjoin_tateModule_apply_mem_and_comp_tateModuleRep_eq.solution
