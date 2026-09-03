import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn

set_option autoImplicit false

theorem PDivisibleGroup.exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} (H : PDivisibleGroup O p h) :
    (∃ S : Submodule ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))),
      (∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ S ↔
        ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ∧
      ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), (p : ℤ_[p]) • y ∈ S → y ∈ S) ∧
    ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) → τ ∈ P.inertiaSubgroupIn ℚ →
      ∀ x : TateModule p (H.Points (AlgebraicClosure ℚ)),
        ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            ((H.tateModuleRep (AlgebraicClosure ℚ) τ' x - x :
              TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1 := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn.solution
