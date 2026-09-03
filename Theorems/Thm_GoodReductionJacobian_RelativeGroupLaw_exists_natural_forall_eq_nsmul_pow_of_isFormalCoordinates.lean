import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates
    {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀))
    (μ : ℕ) (hμ : RingHom.ker (algebraMap B B₀) ^ (μ + 1) = ⊥) (N : ℕ) (hN : (N : B) = 0)

    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of B)} [Smooth f'] (L' : RelativeGroupLaw B f')
    (hc : L'.IsCommutative) {d : ℕ} (F : MvFormalGroup d B) (θ : RelativeGroupLaw.FormalCoordinates f' d)
    (hθ : L'.IsFormalCoordinates F θ)

    {Z Z₀ : Scheme.{0}} (fZ : Z ⟶ Spec (CommRingCat.of B)) (fZ₀ : Z₀ ⟶ Spec (CommRingCat.of B₀)) (g : Z₀ ⟶ Z)
    (hg : CategoryTheory.IsPullback g fZ₀ fZ (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (ψ : Z₀ ⟶ A') (hψ : ψ ≫ f' = fZ₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) :
    ∃ Ñ : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z),
        P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)) → (Spec (CommRingCat.of C) ⟶ A'),

      (∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
        (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))),
        Ñ C P hP ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B C))) ∧

      (∀ (C C' : Type) [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C'] (φ : C →ₐ[B] C')
        (P : Spec (CommRingCat.of C) ⟶ Z) (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (hP' : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P) ≫ fZ =
          Spec.map (CommRingCat.ofHom (algebraMap B C'))),
        Ñ C' (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P) hP' =
          Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Ñ C P hP) ∧

      (∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
        (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (P₀ : Spec (CommRingCat.of (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C))) ⟶ Z₀)
        (hP₀ : P₀ ≫ g =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ P)
        (x : Spec (CommRingCat.of C) ⟶ A') (hx : x ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (hlift : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ x =
          P₀ ≫ ψ),
        Ñ C P hP = (L'.nsmul (Spec.map (CommRingCat.ofHom (algebraMap B C))) (N ^ μ) ⟨x, hx⟩).1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates.solution
