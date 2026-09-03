import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq

theorem WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) (n : ℤ) (c : R) : (W.Φ n - Polynomial.C c * W.ΨSq n).natDegree = n.natAbs ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq.solution
