import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_isPullback

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

theorem solution
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {M M' : A.Modules} (h : LocIsoOnBase f M M') :
    LocIsoOnBase f' ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj M') := by
  intro s'
  obtain ⟨U, hs, ⟨e⟩⟩ := h ((Spec.map (CommRingCat.ofHom φ)).base s')
  refine ⟨Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U, hs, ⟨?_⟩⟩
  have hle : f' ⁻¹ᵁ (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U) ≤ g ⁻¹ᵁ (f ⁻¹ᵁ U) :=
    le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hg.w])
  have hρ := Scheme.Hom.resLE_comp_ι g hle
  exact (Scheme.Modules.pullbackComp _ g).app M ≪≫
    (Scheme.Modules.pullbackCongr hρ.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (g.resLE (f ⁻¹ᵁ U) _ hle) (f ⁻¹ᵁ U).ι).app M).symm ≪≫
    (Scheme.Modules.pullback (g.resLE (f ⁻¹ᵁ U) _ hle)).mapIso e ≪≫
    (Scheme.Modules.pullbackComp (g.resLE (f ⁻¹ᵁ U) _ hle) (f ⁻¹ᵁ U).ι).app M' ≪≫
    (Scheme.Modules.pullbackCongr hρ).app M' ≪≫
    ((Scheme.Modules.pullbackComp _ g).app M').symm
