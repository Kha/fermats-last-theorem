import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor.AlgebraicGeometry AlgebraicGeometry.Polarisation P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor.AlgebraicGeometry.Polarisation"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Polarisation.LocIsoOnBase Scheme.Modules.pullbackTensorObjIso"
namespace Polarisation
p2m_export "AlgebraicGeometry.Polarisation" "LocIsoOnBase"
namespace LocIsoOnBaseTensorSol
p2m_open "AlgebraicGeometry.Polarisation AlgebraicGeometry"

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S))

def restrictIso {M M' : X.Modules} {U V : (Spec (CommRingCat.of S)).Opens} (hVU : V ≤ U)
    (e : (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M') :
    (Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj M' :=
  have hle : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U := fun _ hx => hVU hx
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE hle) (g ⁻¹ᵁ U).ι).app M).symm ≪≫
      (Scheme.Modules.pullback (X.homOfLE hle)).mapIso e ≪≫
        (Scheme.Modules.pullbackComp (X.homOfLE hle) (g ⁻¹ᵁ U).ι).app M' ≪≫
          (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle)).app M'

end AlgebraicGeometry.Polarisation.LocIsoOnBaseTensorSol

open AlgebraicGeometry.Polarisation.LocIsoOnBaseTensorSol in
theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of S)}
    {M M' N N' : X.Modules} (hM : LocIsoOnBase g M M') (hN : LocIsoOnBase g N N') :
    LocIsoOnBase g (M ⊗ N) (M' ⊗ N') := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := hM s
  obtain ⟨U', hs', ⟨e'⟩⟩ := hN s
  refine ⟨U ⊓ U', ⟨hs, hs'⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackTensorObjIso (g ⁻¹ᵁ (U ⊓ U')).ι M N ≪≫
    (restrictIso g inf_le_left e ⊗ᵢ restrictIso g inf_le_right e') ≪≫
      (Scheme.Modules.pullbackTensorObjIso (g ⁻¹ᵁ (U ⊓ U')).ι M' N').symm

end
