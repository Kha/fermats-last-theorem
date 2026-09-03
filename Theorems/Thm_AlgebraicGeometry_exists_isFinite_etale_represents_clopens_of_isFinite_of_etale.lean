import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isFinite_etale_represents_clopens_of_isFinite_of_etale

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isFinite_etale_represents_clopens_of_isFinite_of_etale
    (S : Type) [CommRing S] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of S)) [IsFinite p] [Etale p]
    (r : ℕ) (hr : ∀ s : ↥(Spec (CommRingCat.of S)), p.finrank s = r) :
    ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of S)) (_ : IsFinite ζ) (_ : Etale ζ)
      (ptZ : ∀ (T : Type) [CommRing T] (φ : S →+* T) (X' : Scheme.{0}) (p' : X' ⟶ Spec (CommRingCat.of T))
        (g : X' ⟶ X), IsPullback g p' p (Spec.map (CommRingCat.ofHom φ)) →
        ∀ U : X'.Opens, IsClosed (U : Set ↥X') → (Spec (CommRingCat.of T) ⟶ Z)),

      (∀ (T : Type) [CommRing T] (φ : S →+* T) (X' : Scheme.{0}) (p' : X' ⟶ Spec (CommRingCat.of T))
          (g : X' ⟶ X) (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ)))
          (U : X'.Opens) (hU : IsClosed (U : Set ↥X')),
          ptZ T φ X' p' g h U hU ≫ ζ = Spec.map (CommRingCat.ofHom φ)) ∧

      (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : S →+* T) (ψ : T →+* T')
          (X' : Scheme.{0}) (p' : X' ⟶ Spec (CommRingCat.of T)) (g : X' ⟶ X)
          (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ)))
          (X'' : Scheme.{0}) (p'' : X'' ⟶ Spec (CommRingCat.of T')) (g' : X'' ⟶ X)
          (h' : IsPullback g' p'' p (Spec.map (CommRingCat.ofHom (ψ.comp φ))))
          (k : X'' ⟶ X'), k ≫ p' = p'' ≫ Spec.map (CommRingCat.ofHom ψ) → k ≫ g = g' →
          ∀ (U : X'.Opens) (hU : IsClosed (U : Set ↥X')) (U' : X''.Opens) (hU' : IsClosed (U' : Set ↥X'')),
            k ⁻¹ᵁ U = U' →
            ptZ T' (ψ.comp φ) X'' p'' g' h' U' hU' = Spec.map (CommRingCat.ofHom ψ) ≫ ptZ T φ X' p' g h U hU) ∧

      (∀ (T : Type) [CommRing T] (φ : S →+* T) (X' : Scheme.{0}) (p' : X' ⟶ Spec (CommRingCat.of T))
          (g : X' ⟶ X) (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ)))
          (z : Spec (CommRingCat.of T) ⟶ Z), z ≫ ζ = Spec.map (CommRingCat.ofHom φ) →
          ∃ (U : X'.Opens) (hU : IsClosed (U : Set ↥X')), ptZ T φ X' p' g h U hU = z) ∧

      (∀ (T : Type) [CommRing T] (φ : S →+* T) (X' : Scheme.{0}) (p' : X' ⟶ Spec (CommRingCat.of T))
          (g : X' ⟶ X) (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ)))
          (U U' : X'.Opens) (hU : IsClosed (U : Set ↥X')) (hU' : IsClosed (U' : Set ↥X')),
          ptZ T φ X' p' g h U hU = ptZ T φ X' p' g h U' hU' → U = U') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isFinite_etale_represents_clopens_of_isFinite_of_etale.solution
