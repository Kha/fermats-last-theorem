import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_CompletedPoints
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
attribute [-instance] PrimaryTorsion.instSMul PrimaryTorsion.instModule
attribute [-simp] PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (Ker G₁ Inv : Set (G.CPoints (integralClosure R (PadicAlgCl p))))
    (hKer : ∀ Y, Y ∈ Ker ↔
      ∀ (y : TateModule p (G'.Points (PadicAlgCl p))) (i w : ℕ), i ≤ w →
        ∀ (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
            Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i}) w),
          G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) i Y →
        ∀ (ψ : G'.Point (integralClosure R (PadicAlgCl p)) w),
          G'.pointsMkAdd (PadicAlgCl p) w
              (Additive.ofMul (G'.pointMap (integralClosure R (PadicAlgCl p)).val w ψ)) =
            (y : ℕ → G'.Points (PadicAlgCl p)) w →
          D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R
              (Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i})) w ψ) = 1)
    (hG₁ : ∀ X, X ∈ G₁ ↔
      ∀ (w : ℕ) (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
          Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ 1}) w),
        G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) 1 X →
        ∀ a : G.level w,
          IsNilpotent (PDivisibleGroup.Point.toAlgHom f a - algebraMap R _ (Coalgebra.counit a)))
    (hInv : ∀ X, X ∈ Inv ↔
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (σ' : integralClosure R (PadicAlgCl p) ≃ₐ[R] integralClosure R (PadicAlgCl p)),
        (∀ a : integralClosure R (PadicAlgCl p),
            ((σ' a : integralClosure R (PadicAlgCl p)) : PadicAlgCl p) = σ a) →
        σ' • X = X) :
    (∀ Y ∈ Ker, ∀ n : ℕ, n • Y ∈ Ker) ∧
    (∀ Y ∈ Ker, ∀ k : ℕ, p ^ k • Y = 0 → Y = 0) ∧
    (∀ X ∈ Ker, X ∈ G₁ → X ∈ Inv → ∃ X₁ ∈ Ker, X₁ ∈ G₁ ∧ X₁ ∈ Inv ∧ p • X₁ = X) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff.solution
