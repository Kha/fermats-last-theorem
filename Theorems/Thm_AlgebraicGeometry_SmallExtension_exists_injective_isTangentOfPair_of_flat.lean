import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing~exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot TensorProduct"

universe u

theorem AlgebraicGeometry.SmallExtension.exists_injective_isTangentOfPair_of_flat
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) [Flat q]

    {Y₀ : Scheme.{u}} (i₀ : Y₀ ⟶ Y) (q₀ : Y₀ ⟶ Spec (CommRingCat.of (T' ⧸ I)))
    (h₀ : IsPullback i₀ q₀ q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))

    {Yk : Scheme.{u}} (ik : Yk ⟶ Y) (f₀ : Yk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hk : IsPullback ik f₀ q (Spec.map (CommRingCat.ofHom (residue T'))))
    {Z : Scheme.{u}} (q₁ : Z ⟶ Yk) (q₂ : Z ⟶ SquareZero.spec (ResidueField T') V)
    (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase (ResidueField T') V))
    :
    ∃ Φ : ∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q),
        {v : Y ⟶ A // v ≫ pA = q ∧ i₀ ≫ v = i₀ ≫ u} →
          {w : Z ⟶ A // SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w = ik ≫ u},

      (∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q),
        Function.Injective (Φ pA u hu)) ∧

      (∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q),
        (Φ pA u hu ⟨u, hu, rfl⟩).1 = q₁ ≫ ik ≫ u) ∧

      (∀ {A A' : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (pA' : A' ⟶ Spec (CommRingCat.of T'))
        (g : A ⟶ A') (hg : g ≫ pA' = pA) (u : Y ⟶ A) (hu : u ≫ pA = q)
        (v : {v : Y ⟶ A // v ≫ pA = q ∧ i₀ ≫ v = i₀ ≫ u}),
        (Φ pA' (u ≫ g) (by rw [Category.assoc, hg, hu])
            ⟨v.1 ≫ g, by rw [Category.assoc, hg, v.2.1], by rw [← Category.assoc, v.2.2, Category.assoc]⟩).1 =
          (Φ pA u hu v).1 ≫ g) ∧

      ∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q)
        (v : {v : Y ⟶ A // v ≫ pA = q ∧ i₀ ≫ v = i₀ ≫ u})
        (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
        (c : Spec (CommRingCat.of C) ⟶ Y) (hc : c ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' C))),
        (∃ U : Y.Opens, IsAffineOpen U ∧ Set.range c.base ⊆ (U : Set Y)) →
        ∀ (cZ : Spec (CommRingCat.of (SmallExtension.thickening T' V C)) ⟶ Z),
        cZ ≫ q₁ ≫ ik = SmallExtension.thickeningFst T' V C ≫
          Spec.map (CommRingCat.ofHom (SmallExtension.toReduction T' C)) ≫ c →
        cZ ≫ q₂ = SmallExtension.thickeningSnd T' V C →
        SmallExtension.IsTangentOfPair I V ι C (c ≫ u) (c ≫ v.1) (cZ ≫ (Φ pA u hu v).1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat.solution
