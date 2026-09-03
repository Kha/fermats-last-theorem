import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_exists_isFibreReading_and_cocycle_one_add_of_forall_d_eq_zero
attribute [-instance] PresheafOfModules.ExteriorPower.instModulePresheafAb
attribute [-simp] AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension~isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading~exists_mem_map_range_and_isFibreReading_of_isAffineOpen Scheme.TwoAffineOpenCover"

universe u

theorem AlgebraicGeometry.SmallExtension.exists_isFibreReading_and_cocycle_one_add_of_forall_d_eq_zero
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π)
    (hsmall : RingHom.ker π * maximalIdeal B₁ = ⊥) (hI : RingHom.ker π ≤ maximalIdeal B₁)

    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker π))

    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [IsSeparated f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X) [IsAffineHom g]
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X) [IsAffineHom i]
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (𝒰 : X.OrderedAffineCover)
    (w : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : ∀ ξ : Module.Dual (ResidueField B₁) V, (OModulePresheaf.unit fk).d (𝒰.comap i) 1 (w ξ) = 0) :
    ∃ ε : ∀ s : 𝒰.Idx 1, Γ(X, 𝒰.inter s),
      (∀ s : 𝒰.Idx 1,
        IsFibreReading V ι f fk i (𝒰.inter s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s) (ε s)
          ((LinearMap.proj s).comp w)) ∧
      (∀ s : 𝒰.Idx 1, (1 + ε s) * (1 - ε s) = 1) ∧
      (∀ r : 𝒰.Idx 2,
        (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (1 + ε (𝒰.face r 2)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (1 + ε (𝒰.face r 0)) =
          (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (1 + ε (𝒰.face r 1))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_exists_isFibreReading_and_cocycle_one_add_of_forall_d_eq_zero.solution
