import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u
theorem AlgebraicGeometry.SmallExtension.exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    (hI : RingHom.ker π ≤ maximalIdeal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    (Ua Ub : A₀.Opens)
    {Ya Yb : Scheme.{u}} (qa : Ya ⟶ Spec (CommRingCat.of T')) (qb : Yb ⟶ Spec (CommRingCat.of T')) (hqa : Smooth qa)
    (ga : (↑Ua : Scheme.{u}) ⟶ Ya) (gb : (↑Ub : Scheme.{u}) ⟶ Yb)
    (hgb : IsPullback gb (Ub.ι ≫ f₀) qb (Spec.map (CommRingCat.ofHom π)))
    (Oa : A₀.Opens → Ya.Opens) (Ob : A₀.Opens → Yb.Opens)
    (hOb : ∀ W : A₀.Opens, gb ⁻¹ᵁ Ob W = Ub.ι ⁻¹ᵁ W)
    (hOaffa : IsAffineOpen (Oa (Ua ⊓ Ub))) (hOaffb : IsAffineOpen (Ob (Ua ⊓ Ub)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Yb)
    (haW : IsPullback aW (W.ι ≫ fk) qb (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (φ : (↑(Oa (Ua ⊓ Ub)) : Scheme.{u}) ≅ ↑(Ob (Ua ⊓ Ub)))
    (hφq : φ.hom ≫ (Ob (Ua ⊓ Ub)).ι ≫ qb = (Oa (Ua ⊓ Ub)).ι ≫ qa)
    (hφg : ∃ (γ : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Oa (Ua ⊓ Ub))) (γ' : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Ob (Ua ⊓ Ub))),
        γ ≫ (Oa (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_left ≫ ga ∧
        γ' ≫ (Ob (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_right ≫ gb ∧
        γ ≫ φ.hom = γ')
    (hφO : ∀ W' : A₀.Opens, φ.hom ⁻¹ᵁ ((Ob (Ua ⊓ Ub)).ι ⁻¹ᵁ Ob W') = (Oa (Ua ⊓ Ub)).ι ⁻¹ᵁ Oa W')

    (δ : letI := algebraOfHom qa (Oa (Ua ⊓ Ub)); letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(Ya, Oa (Ua ⊓ Ub)))))) :
    letI := algebraOfHom qa (Oa (Ua ⊓ Ub)); letI := algebraOfHom fk Ue
    ∃ φ' : (↑(Oa (Ua ⊓ Ub)) : Scheme.{u}) ≅ ↑(Ob (Ua ⊓ Ub)),
      φ'.hom ≫ (Ob (Ua ⊓ Ub)).ι ≫ qb = (Oa (Ua ⊓ Ub)).ι ≫ qa ∧
      (∃ (γ : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Oa (Ua ⊓ Ub))) (γ' : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Ob (Ua ⊓ Ub))),
        γ ≫ (Oa (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_left ≫ ga ∧
        γ' ≫ (Ob (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_right ≫ gb ∧
        γ ≫ φ'.hom = γ') ∧
      (∀ W' : A₀.Opens, φ'.hom ⁻¹ᵁ ((Ob (Ua ⊓ Ub)).ι ⁻¹ᵁ Ob W') = (Oa (Ua ⊓ Ub)).ι ⁻¹ᵁ Oa W') ∧
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Ya, Oa (Ua ⊓ Ub))
        (hOaffa.isoSpec.inv ≫ φ.hom ≫ (Ob (Ua ⊓ Ub)).ι)
        (hOaffa.isoSpec.inv ≫ φ'.hom ≫ (Ob (Ua ⊓ Ub)).ι)
        fk Lk W aW Ue
        (fun x => (δ : Γ(Ak, Ue) →ₗ[ResidueField T']
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(Ya, Oa (Ua ⊓ Ub))))) x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations.solution
