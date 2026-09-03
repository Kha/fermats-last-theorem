import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic
    (p : ℕ) [Fact p.Prime]
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] [Module.Free ℤ_[p] B]
    [Algebra.Etale ℤ_[p] B]
    [Algebra B (AlgebraicClosure ℚ_[p])] [IsScalarTower ℤ_[p] B (AlgebraicClosure ℚ_[p])]
    (H : Type) [CommRing H] [HopfAlgebra B H] [Module.Finite B H] [Module.Free B H] [Coalgebra.IsCocomm B H]
    (W : Type) [CommRing W] [HopfAlgebra ℤ_[p] W]
    (e : ∀ (T : Type) [CommRing T] [Algebra ℤ_[p] T],
      WithConv (W →ₐ[ℤ_[p]] T) ≃ WithConv (H →ₐ[B] (B ⊗[ℤ_[p]] T)))
    (he_mul : ∀ (T : Type) [CommRing T] [Algebra ℤ_[p] T] (f g : WithConv (W →ₐ[ℤ_[p]] T)),
      e T (f * g) = e T f * e T g)
    (he_nat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ_[p] T] [CommRing T'] [Algebra ℤ_[p] T'] (u : T →ₐ[ℤ_[p]] T')
      (f : WithConv (W →ₐ[ℤ_[p]] T)),
      e T' (WithConv.toConv (u.comp f.ofConv))
        = WithConv.toConv ((Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f).ofConv)) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) P)
      (eW : WithConv (W →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ P)
      (π₀ : P →+ Additive (WithConv (H →ₐ[B] AlgebraicClosure ℚ_[p]))),
      (∀ f g, eW (f * g) = eW f + eW g) ∧
      (∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (f g : WithConv (W →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
        (∀ x : W, g x = σ (f x)) → eW g = σ • (eW f)) ∧
      (∀ f : WithConv (W →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
        Additive.toMul (π₀ (eW f)) = WithConv.toConv
          ((Algebra.TensorProduct.lift (Algebra.ofId B (AlgebraicClosure ℚ_[p])) (AlgHom.id ℤ_[p] (AlgebraicClosure ℚ_[p]))
            (fun _ _ => Commute.all _ _)).comp (e (AlgebraicClosure ℚ_[p]) f).ofConv)) ∧
      (∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]), (∀ b : B, σ (algebraMap B (AlgebraicClosure ℚ_[p]) b) = algebraMap B (AlgebraicClosure ℚ_[p]) b) →
        ∀ (x : P) (g : WithConv (H →ₐ[B] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (Additive.toMul (π₀ x) h)) → π₀ (σ • x) = Additive.ofMul g) ∧
      (∀ x : P, (∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], π₀ (σ • x) = 0) → x = 0) ∧
      (∀ f : WithConv (H →ₐ[B] AlgebraicClosure ℚ_[p]), ∃ x : P, π₀ x = Additive.ofMul f ∧
        ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], (∃ b : B, σ (algebraMap B (AlgebraicClosure ℚ_[p]) b) ≠ algebraMap B (AlgebraicClosure ℚ_[p]) b) →
          π₀ (σ • x) = 0) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic.solution
