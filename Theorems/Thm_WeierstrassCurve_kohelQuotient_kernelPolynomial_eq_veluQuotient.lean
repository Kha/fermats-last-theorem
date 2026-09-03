import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_KernelPolynomial
import Definitions.Def_WeierstrassCurve_KohelQuotient
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_kohelQuotient_kernelPolynomial_eq_veluQuotient

theorem WeierstrassCurve.kohelQuotient_kernelPolynomial_eq_veluQuotient
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (S : Finset (R × R))
    (hS : ∀ P ∈ S, W.toAffine.Equation P.1 P.2) :
    W.kohelQuotient (WeierstrassCurve.kernelPolynomial S) = W.veluQuotient S := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_kohelQuotient_kernelPolynomial_eq_veluQuotient.solution
