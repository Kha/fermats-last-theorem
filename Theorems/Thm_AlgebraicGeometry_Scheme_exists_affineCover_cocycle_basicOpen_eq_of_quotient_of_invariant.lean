import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant
    (X Y : Scheme.{0}) (Γ : Type) [Group Γ] (ρ : Γ →* Aut X)
    (q : X ⟶ Y) (hq : ∀ γ : Γ, (ρ γ).hom ≫ q = q) (hsurj : Function.Surjective q.base)
    (hinj : ∀ V : Y.Opens, Function.Injective (q.app V))
    (hrange : ∀ V : Y.Opens, Set.range (q.app V) =
      {t | ∀ γ : Γ, (ρ γ).hom.appLE (q ⁻¹ᵁ V) (q ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hq γ]) t = t})
    (hdesc : ∀ U : X.Opens, IsAffineOpen U → (∀ γ : Γ, (ρ γ).hom ⁻¹ᵁ U = U) → ∃ V : Y.Opens, IsAffineOpen V ∧ q ⁻¹ᵁ V = U)
    (r : ℕ) (U : Fin r → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i))
    (hinv : ∀ (γ : Γ) (i : Fin r), (ρ γ).hom ⁻¹ᵁ U i = U i) (hcov : (⨆ i, U i) = ⊤)
    (w : ∀ i j : Fin r, Γ(X, U i)) (hw1 : ∀ i, w i i = 1)
    (hw2 : ∀ i j k : Fin r,
      X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i k) =
        X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i j) *
          X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (w j k))
    (hw3 : ∀ i j : Fin r, X.basicOpen (w i j) = U i ⊓ U j)
    (hw4 : ∀ (γ : Γ) (i j : Fin r), (ρ γ).hom.appLE (U i) (U i) (le_of_eq (hinv γ i).symm) (w i j) = w i j) :
    ∃ (V : Fin r → Y.Opens) (v : ∀ i j : Fin r, Γ(Y, V i)),
      (∀ i, IsAffineOpen (V i)) ∧ (∀ i, q ⁻¹ᵁ V i = U i) ∧ (⨆ i, V i) = ⊤ ∧
      (∀ i, v i i = 1) ∧
      (∀ i j k : Fin r,
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (v i k) =
          Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (v i j) *
            Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (v j k)) ∧
      (∀ i j : Fin r, Y.basicOpen (v i j) = V i ⊓ V j) ∧
      (∀ (i j : Fin r) (e : U i ≤ q ⁻¹ᵁ V i), q.appLE (V i) (U i) e (v i j) = w i j) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.solution
