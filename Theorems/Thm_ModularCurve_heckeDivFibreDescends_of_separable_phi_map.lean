import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeDivFibreDescends_of_separable_phi_map
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false
theorem ModularCurve.heckeDivFibreDescends_of_separable_phi_map (k : Type*) [Field k]
    (N q : ℕ) [NeZero N] [NeZero q] [Fact q.Prime]
    (data : ModularCurve.ModularPolynomialData q) (hsymm : ModularCurve.EvalSymm data.Φ)
    (hqk : (q : k) ≠ 0)
    (hsep : ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    ModularCurve.HeckeDivFibreDescends k N q := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeDivFibreDescends_of_separable_phi_map.solution
