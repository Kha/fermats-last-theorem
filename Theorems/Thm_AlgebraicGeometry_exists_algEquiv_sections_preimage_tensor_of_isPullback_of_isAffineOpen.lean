import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen TensorProduct"

universe u

theorem AlgebraicGeometry.exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H]
    {B : Scheme.{u}} (fB : B ⟶ Spec (CommRingCat.of H)) (π : B ⟶ A)
    (hB : IsPullback π fB f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKB : ∀ W : B.Opens, Algebra K Γ(B, W) := fun W => Scheme.TwoAffineOpenCover.algebraOfHom (π ≫ f) W
    ∃ ε : ∀ (V : A.Opens) (_ : IsAffineOpen V), Γ(B, π ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H,
      (∀ (V : A.Opens) (hV : IsAffineOpen V), IsAffineOpen (π ⁻¹ᵁ V)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)), ε V hV ((π.app V).hom a) = a ⊗ₜ[K] (1 : H)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
          ε V hV ((fB.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) =
            (1 : Γ(A, V)) ⊗ₜ[K] h) ∧
      (∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V) (s : Γ(B, π ⁻¹ᵁ V)),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
            ε V' hV' ((B.presheaf.map (homOfLE (π.preimage_mono hle)).op).hom s)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.solution
