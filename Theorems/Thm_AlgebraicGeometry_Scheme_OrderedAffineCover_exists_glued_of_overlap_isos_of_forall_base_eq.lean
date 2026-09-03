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
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_glued_of_overlap_isos_of_forall_base_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_glued_of_overlap_isos_of_forall_base_eq
    {X₀ S : Scheme.{0}} (p : X₀ ⟶ S) (𝒰 : X₀.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hτS : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ p = (𝒰.inter s).ι ≫ p)
    (hτpt : ∀ (s : 𝒰.Idx 1) (x : ↑(𝒰.inter s)), (τ s).hom.base x = x)
    (hcoc : ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ X₀.homOfLE (𝒰.inter_le_inter_face r j)
            = X₀.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0) :
    ∃ (X : Scheme.{0}) (fX : X ⟶ S) (ιU : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ X),
      (∀ i, IsOpenImmersion (ιU i)) ∧
      (∀ i, ιU i ≫ fX = (𝒰.U i).ι ≫ p) ∧
      (∀ x : X, ∃ (i : 𝒰.ι) (y : ↑(𝒰.U i)), (ιU i).base y = x) ∧
      (∀ s : 𝒰.Idx 1,
        X₀.homOfLE (𝒰.inter_le s 0) ≫ ιU (s.1 0) = (τ s).hom ≫ X₀.homOfLE (𝒰.inter_le s 1) ≫ ιU (s.1 1)) ∧
      (∀ (i j : 𝒰.ι) (y : ↑(𝒰.U i)) (y' : ↑(𝒰.U j)),
        (ιU i).base y = (ιU j).base y' ↔ (𝒰.U i).ι.base y = (𝒰.U j).ι.base y') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_glued_of_overlap_isos_of_forall_base_eq.solution
