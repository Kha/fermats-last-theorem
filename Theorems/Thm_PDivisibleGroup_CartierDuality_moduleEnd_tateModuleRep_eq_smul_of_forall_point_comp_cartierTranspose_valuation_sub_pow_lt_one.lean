import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_moduleEnd_tateModuleRep_eq_smul_of_forall_point_comp_cartierTranspose_valuation_sub_pow_lt_one

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.moduleEnd_tateModuleRep_eq_smul_of_forall_point_comp_cartierTranspose_valuation_sub_pow_lt_one
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} {H H' : PDivisibleGroup O p h} (D : H.CartierDuality H')
    (B : TateModule p (H.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (H'.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (Additive (AlgebraicClosure ℚ)ˣ))
    (hB : ∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (y : TateModule p (H'.Points (AlgebraicClosure ℚ))) (v : ℕ)
        (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v),
        H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) v →
        H'.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul ψ) = (y : ℕ → H'.Points (AlgebraicClosure ℚ)) v →
        ((Additive.toMul ((B x y : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) : (AlgebraicClosure ℚ)) = D.pair (AlgebraicClosure ℚ) v f ψ)
    (φ' : (AlgebraicClosure ℚ) ≃ₐ[O] (AlgebraicClosure ℚ)) (c : ℤ_[p])
    (a ε : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (ha : ∀ v : ℕ, (H.transition v).comp (a (v + 1)) = (a v).comp (H.transition v))
    (hε : ∀ v : ℕ, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
    (hεε : ∀ v : ℕ, (ε v).comp (ε v) = ε v)
    (hεa : ∀ v : ℕ, (ε v).comp (a v) = (a v).comp (ε v))
    (Aop Eop : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (hA : (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
      ((Aop x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom f).comp (a w : H.level w →ₐ[O] H.level w))))))
    (hE : (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
      ((Eop x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom f).comp (ε w : H.level w →ₐ[O] H.level w))))))
    (htwist : ∀ (v : ℕ) (ψ : H'.Point (AlgebraicClosure ℚ) v),
      (∀ c : H'.level v, PDivisibleGroup.Point.toAlgHom ψ c ∈ P) →
      (PDivisibleGroup.Point.toAlgHom ψ).comp (((D.equiv v).symm : CartierDual O (H.level v) →ₐc[O] H'.level v).comp
          ((CartierDual.map (ε v)).comp (D.equiv v : H'.level v →ₐc[O] CartierDual O (H.level v))) :
            H'.level v →ₐ[O] H'.level v) = PDivisibleGroup.Point.toAlgHom ψ →
      ∀ c : H'.level v,
        P.valuation ((PDivisibleGroup.Point.toAlgHom ψ).comp (((D.equiv v).symm : CartierDual O (H.level v) →ₐc[O] H'.level v).comp
          ((CartierDual.map (a v)).comp (D.equiv v : H'.level v →ₐc[O] CartierDual O (H.level v))) :
            H'.level v →ₐ[O] H'.level v) c -
          PDivisibleGroup.Point.toAlgHom ψ c ^ p) < 1)

    (hfrob : ∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))),
      (∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
        ∀ c : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f c -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1) →
      Eop x = x →
      ∀ (y z : TateModule p (H'.Points (AlgebraicClosure ℚ))),
        (∀ n : ℕ, ∃ (w : ℕ) (ψ χ : H'.Point (AlgebraicClosure ℚ) w),
          H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul ψ) = (y : ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
          H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul χ) = (z : ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
          (∀ c : H'.level w, PDivisibleGroup.Point.toAlgHom ψ c ∈ P) ∧
          (∀ c : H'.level w, P.valuation (PDivisibleGroup.Point.toAlgHom χ c -
            PDivisibleGroup.Point.toAlgHom ψ c ^ p) < 1) ∧
          (PDivisibleGroup.Point.toAlgHom ψ).comp (((D.equiv w).symm : CartierDual O (H.level w) →ₐc[O] H'.level w).comp
              ((CartierDual.map (ε w)).comp (D.equiv w : H'.level w →ₐc[O] CartierDual O (H.level w))) :
                H'.level w →ₐ[O] H'.level w) = PDivisibleGroup.Point.toAlgHom ψ ∧
          (PDivisibleGroup.Point.toAlgHom χ).comp (((D.equiv w).symm : CartierDual O (H.level w) →ₐc[O] H'.level w).comp
              ((CartierDual.map (ε w)).comp (D.equiv w : H'.level w →ₐc[O] CartierDual O (H.level w))) :
                H'.level w →ₐ[O] H'.level w) = PDivisibleGroup.Point.toAlgHom χ) →
        B (H.tateModuleRep (AlgebraicClosure ℚ) φ' x) z = c • B x y)

    (x : TateModule p (H.Points (AlgebraicClosure ℚ)))
    (hx : ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      ∀ c : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f c -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1)
    (hEx : Eop x = x) :
    Aop (H.tateModuleRep (AlgebraicClosure ℚ) φ' x) = c • x := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_moduleEnd_tateModuleRep_eq_smul_of_forall_point_comp_cartierTranspose_valuation_sub_pow_lt_one.solution
