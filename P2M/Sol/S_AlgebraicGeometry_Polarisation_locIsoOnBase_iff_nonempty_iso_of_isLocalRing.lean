import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation

theorem solution
    {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S)) (M M' : X.Modules) :
    LocIsoOnBase g M M' ↔ Nonempty (M ≅ M') := by
  classical
  constructor
  · intro h
    obtain ⟨U, hsU, ⟨e⟩⟩ := h (IsLocalRing.closedPoint S)
    have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hsU
    subst hU

    let ι : (↑(g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of S)).Opens)) : Scheme.{0}) ⟶ X := (g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of S)).Opens)).ι
    let j : X ⟶ ↑(g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of S)).Opens)) := (Scheme.topIso X).inv
    have hj : j ≫ ι = 𝟙 X := (Scheme.topIso X).inv_hom_id
    let Φ : 𝟭 X.Modules ≅ Scheme.Modules.pullback ι ⋙ Scheme.Modules.pullback j :=
      (Scheme.Modules.pullbackId X).symm ≪≫ eqToIso (by rw [hj]) ≪≫ (Scheme.Modules.pullbackComp j ι).symm
    exact ⟨Φ.app M ≪≫ (Scheme.Modules.pullback j).mapIso e ≪≫ (Φ.app M').symm⟩
  · rintro ⟨e⟩ s
    exact ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩
