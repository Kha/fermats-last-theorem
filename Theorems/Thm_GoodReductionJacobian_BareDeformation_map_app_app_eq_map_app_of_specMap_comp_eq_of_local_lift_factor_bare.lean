import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_map_app_app_eq_map_app_of_specMap_comp_eq_of_local_lift_factor_bare

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.map_app_app_eq_map_app_of_specMap_comp_eq_of_local_lift_factor_bare
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] (𝒰 : D₀.A.OrderedAffineCover)

    (φ₁ : A₁ ⟶ A₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))
    (ψ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B))))
    (hψ₁ : ψ ≫ jκ = jκ ≫ φ₁)

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)

    (j : 𝒰.ι) (W U' : D₀.A.Opens) (hW : IsAffineOpen W) (hU' : IsAffineOpen U') (hWj : W ≤ 𝒰.U j)
    (p : (↑W : Scheme.{0}) ⟶ ↑U') (hp : p ≫ U'.ι = D₀.A.homOfLE hWj ≫ m j)
    (θ : letI := algebraOfHom D₀.f U'
      letI := algebraOfHom D₀.f W
      Γ(D₀.A, U') →ₐ[B] Γ(D₀.A, W))
    (hθ : letI := algebraOfHom D₀.f U'
      letI := algebraOfHom D₀.f W
      Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ hU'.isoSpec.inv = hW.isoSpec.inv ≫ p)

    (W' U'' : (pullback D₀.f (specMap B (ResidueField B))).Opens)
    (e₁ : U'' ≤ (pullback.fst D₀.f (specMap B (ResidueField B))) ⁻¹ᵁ U') (e₂ : W' ≤ ψ ⁻¹ᵁ U'') (e₃ : W' ≤ (pullback.fst D₀.f (specMap B (ResidueField B))) ⁻¹ᵁ W)
    (y : Γ(D₀.A, U')) :
    letI := algebraOfHom D₀.f U'
    letI := algebraOfHom D₀.f W
    ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE e₂).op).hom
        ((ψ.app U'').hom (((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE e₁).op).hom (((pullback.fst D₀.f (specMap B (ResidueField B))).app U').hom y))) =
      ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE e₃).op).hom (((pullback.fst D₀.f (specMap B (ResidueField B))).app W).hom (θ y)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_map_app_app_eq_map_app_of_specMap_comp_eq_of_local_lift_factor_bare.solution
