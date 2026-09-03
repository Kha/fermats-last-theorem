import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.AlgebraicGeometry AlgebraicGeometry.Polarisation P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.AlgebraicGeometry.Polarisation"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.homOfLE Scheme.Modules Scheme.Modules.pullbackComp Polarisation.LocIsoOnBase"
namespace Polarisation
p2m_export "AlgebraicGeometry.Polarisation" "LocIsoOnBase"
namespace LocIsoOnBaseEquivSol
p2m_open "AlgebraicGeometry.Polarisation AlgebraicGeometry"

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S))

private theorem _root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.refl (M : X.Modules) : LocIsoOnBase g M M :=
  fun _ => ⟨⊤, trivial, ⟨Iso.refl _⟩⟩

p2m_export "AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol" "refl"
variable {g} in
private theorem _root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.symm {M M' : X.Modules} (h : LocIsoOnBase g M M') : LocIsoOnBase g M' M := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := h s
  exact ⟨U, hs, ⟨e.symm⟩⟩

p2m_export "AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol" "symm"

def restrictIso {M M' : X.Modules} {U V : (Spec (CommRingCat.of S)).Opens} (hVU : V ≤ U)
    (e : (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M') :
    (Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj M' :=
  have hle : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U := fun _ hx => hVU hx
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE hle) (g ⁻¹ᵁ U).ι).app M).symm ≪≫
      (Scheme.Modules.pullback (X.homOfLE hle)).mapIso e ≪≫
        (Scheme.Modules.pullbackComp (X.homOfLE hle) (g ⁻¹ᵁ U).ι).app M' ≪≫
          (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle)).app M'

variable {g} in
theorem trans {M M' M'' : X.Modules} (h : LocIsoOnBase g M M') (h' : LocIsoOnBase g M' M'') :
    LocIsoOnBase g M M'' := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := h s
  obtain ⟨U', hs', ⟨e'⟩⟩ := h' s
  exact ⟨U ⊓ U', ⟨hs, hs'⟩, ⟨restrictIso g inf_le_left e ≪≫ restrictIso g inf_le_right e'⟩⟩

end AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol

open AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol in
theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S)) :
    Equivalence (LocIsoOnBase g) :=
  ⟨refl g, symm, trans⟩

end
