import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PDivisibleGroup_CartierDuality
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.CartierDuality.tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} {H H' : PDivisibleGroup O p h} (D : H.CartierDuality H')

    (horth : ∀ (v : ℕ) (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v),
      (∀ a : H.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : H'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      D.pair (AlgebraicClosure ℚ) v f ψ = 1)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ)
    (hττ' : ∀ x : AlgebraicClosure ℚ, τ' x = τ x) (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (x : TateModule p (H.Points (AlgebraicClosure ℚ)))

    (hx : ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :
    H.tateModuleRep (AlgebraicClosure ℚ) τ' x =
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one.solution
