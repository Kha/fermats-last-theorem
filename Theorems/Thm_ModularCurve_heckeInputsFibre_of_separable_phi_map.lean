import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeInputsFibre_of_separable_phi_map
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve AlgebraicCurve in
theorem ModularCurve.heckeInputsFibre_of_separable_phi_map (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q]
    [HasPrincipalDivisors k (charLDegeneracyRoof k N q)] [Fact q.Prime]
    (data : ModularPolynomialData q) (hsymm : EvalSymm data.Φ) (hqk : (q : k) ≠ 0)
    (hsep : ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    HeckeInputsFibre k N q := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeInputsFibre_of_separable_phi_map.solution
