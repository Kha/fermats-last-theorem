import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_ComplexConjugation
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_det_complexConjugation_eq_neg_one_of_detIsCyclotomic

set_option autoImplicit false

theorem ResidualGaloisRep.det_complexConjugation_eq_neg_one_of_detIsCyclotomic
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) :
    LinearMap.det (ρbar.ρ complexConjugation) = -1 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_det_complexConjugation_eq_neg_one_of_detIsCyclotomic.solution
