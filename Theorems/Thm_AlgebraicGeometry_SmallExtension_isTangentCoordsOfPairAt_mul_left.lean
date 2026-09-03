import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_mul_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_mul_left
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T')
    (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T')) (L : RelativeGroupLaw T' qY)
    (u v w : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hw : w ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (hakhom : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t xk),
      (Lk.mul t P Q).1 ≫ ak =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (residue T')))
          ⟨P.1 ≫ ak, by rw [Category.assoc, hak.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ ak, by rw [Category.assoc, hak.w, ← Category.assoc, Q.2]⟩).1)
    (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c) :
    IsTangentCoordsOfPairAt I V ι C
      (L.mul (Spec.map (CommRingCat.ofHom (algebraMap T' C))) ⟨w, hw⟩ ⟨u, hu⟩).1
      (L.mul (Spec.map (CommRingCat.ofHom (algebraMap T' C))) ⟨w, hw⟩ ⟨v, hv⟩).1 xk Lk ak Ue c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_mul_left.solution
