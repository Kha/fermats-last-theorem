import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {K : Type} [Field K] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of K)) (M M' : X.Modules) :
    LocIsoOnBase g M M' ↔ Nonempty (M ≅ M') := by
  constructor
  · intro h
    obtain ⟨U, hsU, ⟨e⟩⟩ := h (IsLocalRing.closedPoint K)

    let V : X.Opens := g ⁻¹ᵁ U
    have hV : ∀ x : X, x ∈ V := by
      intro x
      show g x ∈ U
      rw [Subsingleton.elim (g x) (IsLocalRing.closedPoint K)]
      exact hsU
    haveI : IsIso V.ι := by
      rw [isIso_iff_isOpenImmersion_and_epi_base]
      refine ⟨inferInstance, ?_⟩
      rw [TopCat.epi_iff_surjective]
      intro x
      exact ⟨⟨x, hV x⟩, rfl⟩

    let E : Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.pullback (inv V.ι) ≅ 𝟭 X.Modules :=
      Scheme.Modules.pullbackComp (inv V.ι) V.ι ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id V.ι) ≪≫
        Scheme.Modules.pullbackId X
    exact ⟨(E.app M).symm ≪≫ (Scheme.Modules.pullback (inv V.ι)).mapIso e ≪≫ E.app M'⟩
  · rintro ⟨e⟩ s
    exact ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩
