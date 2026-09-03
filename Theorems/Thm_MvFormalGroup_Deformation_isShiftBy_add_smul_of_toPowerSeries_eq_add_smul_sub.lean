import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_MvFormalGroup_IsShiftBy
import P2M.Util
import P2M.Sol.S_MvFormalGroup_Deformation_isShiftBy_add_smul_of_toPowerSeries_eq_add_smul_sub

set_option autoImplicit false

open IsLocalRing MvFormalGroup
theorem MvFormalGroup.Deformation.isShiftBy_add_smul_of_toPowerSeries_eq_add_smul_sub
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) {d : ℕ} (F : MvFormalGroup d B)
    (G₀ G G' G'' : Deformation (F.map (algebraMap B B₁)) B)
    (w w' : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (a : ResidueField B) (al : B) (hal : residue B al = a)
    (hG'' : ∀ l : Fin d, G''.F.toPowerSeries l = G.F.toPowerSeries l + al • (G'.F.toPowerSeries l - G₀.F.toPowerSeries l))
    (h : Deformation.IsShiftBy V ι F w G₀ G) (h' : Deformation.IsShiftBy V ι F w' G₀ G') :
    Deformation.IsShiftBy V ι F (w + a • w') G₀ G'' := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_Deformation_isShiftBy_add_smul_of_toPowerSeries_eq_add_smul_sub.solution
