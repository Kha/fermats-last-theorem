import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure

set_option autoImplicit false

theorem GaloisRep.exists_finiteFlat_of_subalgebra_pi_algebraicClosure (p : ℕ) (hp : p.Prime)
    {X : Type} [AddCommGroup X] [Finite X]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X]
    (B : Subalgebra (GaloisRep.ratLocalizedAt p) (X → AlgebraicClosure ℚ))
    (hfin : (Subalgebra.toSubmodule B).FG)
    (hequiv : ∀ F ∈ B, ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : X),
      F (σ • x) = σ (F x))
    (hcomul : ∀ F ∈ B, ∃ (n : ℕ) (F₁ F₂ : Fin n → X → AlgebraicClosure ℚ),
      (∀ i, F₁ i ∈ B) ∧ (∀ i, F₂ i ∈ B) ∧ ∀ x y : X, F (x + y) = ∑ i, F₁ i x * F₂ i y)
    (hneg : ∀ F ∈ B, (fun x => F (-x)) ∈ B)
    (hsep : ∀ x y : X, (∀ F ∈ B, F x = F y) → x = y) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ X,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → e g = σ • (e f) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure.solution
