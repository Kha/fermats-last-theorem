import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_tateModule_pairing_rep_eq_cyclotomicCharacter_smul_pairing_of_isFrobeniusAt_of_comp_transition_of_forall_comp_eq_of_forall_valuation_sub_pow_lt_one

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.CartierDuality.tateModule_pairing_rep_eq_cyclotomicCharacter_smul_pairing_of_isFrobeniusAt_of_comp_transition_of_forall_comp_eq_of_forall_valuation_sub_pow_lt_one
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} {H H' : PDivisibleGroup O p h} (D : H.CartierDuality H')

    (ε : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (hεtr : ∀ v : ℕ, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))

    (horth : ∀ (v : ℕ) (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v),
      (∀ a : H.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (PDivisibleGroup.Point.toAlgHom f).comp (ε v : H.level v →ₐ[O] H.level v) =
        PDivisibleGroup.Point.toAlgHom f →
      (∀ a : H'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      D.pair (AlgebraicClosure ℚ) v f ψ = 1)

    (B : TateModule p (H.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]]
      TateModule p (H'.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (Additive (AlgebraicClosure ℚ)ˣ))
    (hB : ∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (y : TateModule p (H'.Points (AlgebraicClosure ℚ)))
        (v : ℕ) (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v),
        H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) v →
        H'.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul ψ) = (y : ℕ → H'.Points (AlgebraicClosure ℚ)) v →
        ((Additive.toMul ((B x y : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) :
          AlgebraicClosure ℚ) = D.pair (AlgebraicClosure ℚ) v f ψ)
    (hBσ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ) (x : TateModule p (H.Points (AlgebraicClosure ℚ)))
        (y : TateModule p (H'.Points (AlgebraicClosure ℚ))) (v : ℕ),
        ((Additive.toMul ((B (H.tateModuleRep (AlgebraicClosure ℚ) σ x)
            (H'.tateModuleRep (AlgebraicClosure ℚ) σ y) : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) :
            (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
          σ (((Additive.toMul ((B x y : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) :
            AlgebraicClosure ℚ)))

    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (φ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ)
    (hφφ' : ∀ t : AlgebraicClosure ℚ, φ' t = φ t) (hφ : P.IsFrobeniusAt φ p)

    (x : TateModule p (H.Points (AlgebraicClosure ℚ)))
    (hx : ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      (∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ∧
      (PDivisibleGroup.Point.toAlgHom f).comp (ε w : H.level w →ₐ[O] H.level w) =
        PDivisibleGroup.Point.toAlgHom f)

    (y z : TateModule p (H'.Points (AlgebraicClosure ℚ)))
    (hyz : ∀ n : ℕ, ∃ (w : ℕ) (ψ χ : H'.Point (AlgebraicClosure ℚ) w),
      H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul ψ) = (y : ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
      H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul χ) = (z : ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
      (∀ a : H'.level w, PDivisibleGroup.Point.toAlgHom ψ a ∈ P) ∧
      ∀ a : H'.level w, P.valuation (PDivisibleGroup.Point.toAlgHom χ a -
        PDivisibleGroup.Point.toAlgHom ψ a ^ p) < 1) :
    B (H.tateModuleRep (AlgebraicClosure ℚ) φ' x) z =
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • B x y := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_tateModule_pairing_rep_eq_cyclotomicCharacter_smul_pairing_of_isFrobeniusAt_of_comp_transition_of_forall_comp_eq_of_forall_valuation_sub_pow_lt_one.solution
