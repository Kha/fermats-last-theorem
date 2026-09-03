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
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_exists_factor_inf_of_local_lifts_factor_bare

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.exists_factor_inf_of_local_lifts_factor_bare
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover)
    (φ₁ : A₁ ⟶ A₁)

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)

    (D : BareDeformation f₁ L₁ B)
    (ιD : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιD i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)

    (mp : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hmpμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mp i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D.g)

    (i i' j j' : 𝒰.ι) (W₀ W₁ : D₀.A.Opens) (h₀ : W₀ ≤ 𝒰.U j) (h₁ : W₁ ≤ 𝒰.U j')
    (n₀ n₀' : (↑W₀ : Scheme.{0}) ⟶ ↑(𝒰.U i)) (n₁ n₁' : (↑W₁ : Scheme.{0}) ⟶ ↑(𝒰.U i'))
    (hn₀ : n₀ ≫ (𝒰.U i).ι = D₀.A.homOfLE h₀ ≫ m j) (hn₀' : n₀' ≫ ιD i = D₀.A.homOfLE h₀ ≫ mp j)
    (hn₁ : n₁ ≫ (𝒰.U i').ι = D₀.A.homOfLE h₁ ≫ m j') (hn₁' : n₁' ≫ ιD i' = D₀.A.homOfLE h₁ ≫ mp j') :
    ∃ (p p' q q' : (↑(W₀ ⊓ W₁) : Scheme.{0}) ⟶ ↑(𝒰.U i ⊓ 𝒰.U i')),
      p ≫ D₀.A.homOfLE inf_le_left = D₀.A.homOfLE inf_le_left ≫ n₀ ∧
      p' ≫ D₀.A.homOfLE inf_le_left = D₀.A.homOfLE inf_le_left ≫ n₀' ∧
      q ≫ D₀.A.homOfLE inf_le_right = D₀.A.homOfLE inf_le_right ≫ n₁ ∧
      q' ≫ D₀.A.homOfLE inf_le_right = D₀.A.homOfLE inf_le_right ≫ n₁' := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_exists_factor_inf_of_local_lifts_factor_bare.solution
