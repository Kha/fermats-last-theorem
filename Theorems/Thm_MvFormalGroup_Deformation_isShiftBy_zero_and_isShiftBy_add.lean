import Mathlib
import Definitions.Def_MvFormalGroup_IsShiftBy
import P2M.Util
import P2M.Sol.S_MvFormalGroup_Deformation_isShiftBy_zero_and_isShiftBy_add

set_option autoImplicit false

open IsLocalRing MvFormalGroup
theorem MvFormalGroup.Deformation.isShiftBy_zero_and_isShiftBy_add
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]
    (w w' : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (G G' G'' : Deformation (F.map (algebraMap B B₁)) B) :
    Deformation.IsShiftBy V ι F 0 G G ∧
      (Deformation.IsShiftBy V ι F w G G' → Deformation.IsShiftBy V ι F w' G' G'' →
        Deformation.IsShiftBy V ι F (w + w') G G'') := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_Deformation_isShiftBy_zero_and_isShiftBy_add.solution
