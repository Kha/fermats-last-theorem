import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_linearMap_tateModule_injective_of_surjective_comp_transition

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_linearMap_tateModule_injective_of_surjective_comp_transition
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    {h h₁ : ℕ} (H : PDivisibleGroup O p h) (H₁ : PDivisibleGroup O p h₁)
    (π : ∀ v : ℕ, H.level v →ₐc[O] H₁.level v) (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1))) :
    ∃ j : TateModule p (H₁.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (H.Points (AlgebraicClosure ℚ)),
      Function.Injective j ∧
      (∀ (x : TateModule p (H₁.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f₁ : H₁.Point (AlgebraicClosure ℚ) w),
        H₁.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f₁) =
          (x : ℕ → H₁.Points (AlgebraicClosure ℚ)) n →
        ((j x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f₁).comp (π w : H.level w →ₐ[O] H₁.level w))))) ∧
      (∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ LinearMap.range j ↔
        ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, π w a = 0 → PDivisibleGroup.Point.toAlgHom f a = 0) ∧
      (∀ τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ,
        j ∘ₗ H₁.tateModuleRep (AlgebraicClosure ℚ) τ' = H.tateModuleRep (AlgebraicClosure ℚ) τ' ∘ₗ j) ∧
      (∀ x : TateModule p (H₁.Points (AlgebraicClosure ℚ)),
        (∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (j x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ↔
        (∀ n : ℕ, ∃ (w : ℕ) (f : H₁.Point (AlgebraicClosure ℚ) w),
          H₁.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (x : ℕ → H₁.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H₁.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_injective_of_surjective_comp_transition.solution
