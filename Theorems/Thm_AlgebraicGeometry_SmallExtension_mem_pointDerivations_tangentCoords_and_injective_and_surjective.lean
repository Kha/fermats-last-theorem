import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover

universe u
theorem AlgebraicGeometry.SmallExtension.mem_pointDerivations_tangentCoords_and_injective_and_surjective
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C]
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (pt : Spec (CommRingCat.of (ResidueField T')) ⟶ Ak) (hpt : pt ≫ xk = 𝟙 _)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = pt) :
    letI := algebraOfHom xk Ue
    (∀ w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
        (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt →
        ∃ D : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
                ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
                (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))),
          ∀ a, D.1 a = tangentCoords T' V C (chartRingHom V C Ue w₁) a) ∧
    (∀ w₁ w₁' : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
        (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt →
        (w₁' ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁' ≫ Ue.ι = reductionBase T' C ≫ pt →
        tangentCoords T' V C (chartRingHom V C Ue w₁) = tangentCoords T' V C (chartRingHom V C Ue w₁') → w₁ = w₁') ∧
    (∀ D : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
                ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
                (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))),
        ∃ w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
          (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) ∧
          SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
              ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt ∧
          ∀ a, D.1 a = tangentCoords T' V C (chartRingHom V C Ue w₁) a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective.solution
