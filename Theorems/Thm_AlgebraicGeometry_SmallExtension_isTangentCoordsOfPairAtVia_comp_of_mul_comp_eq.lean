import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_mul_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_mul_comp_eq
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]

    {Z : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Z)
    {Xk : Scheme.{u}} (fXk : Xk ⟶ Spec (CommRingCat.of (ResidueField T'))) (LX : RelativeGroupLaw (ResidueField T') fXk)
    (WX : Xk.Opens) (aWX : (WX : Scheme.{u}) ⟶ Z) (UXe : Xk.Opens)

    {Y : Scheme.{u}}
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (WA : Ak.Opens) (aWA : (WA : Scheme.{u}) ⟶ Y) (Ue : Ak.Opens)

    (H : Z ⟶ Y)
    (hk : Xk ⟶ Ak) (hhkf : hk ≫ fk = fXk)
    (hhom : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fXk),
      (LX.mul t P Q).1 ≫ hk =
        (Lk.mul t ⟨P.1 ≫ hk, by rw [Category.assoc, hhkf, P.2]⟩ ⟨Q.1 ≫ hk, by rw [Category.assoc, hhkf, Q.2]⟩).1)
    (hUX : UXe ≤ hk ⁻¹ᵁ Ue) (hW : WX ≤ hk ⁻¹ᵁ WA)
    (hcompat : Xk.homOfLE hW ≫ (hk ∣_ WA) ≫ aWA = aWX ≫ H)
    (c : Γ(Xk, UXe) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hc : IsTangentCoordsOfPairAtVia I V ι C u v fXk LX WX aWX UXe c) :
    IsTangentCoordsOfPairAtVia I V ι C (u ≫ H) (v ≫ H) fk Lk WA aWA Ue
      (fun a => c ((Xk.presheaf.map (homOfLE hUX).op).hom ((hk.app Ue).hom a))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_mul_comp_eq.solution
