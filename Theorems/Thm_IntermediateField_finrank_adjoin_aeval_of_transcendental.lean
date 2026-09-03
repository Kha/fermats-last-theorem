import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_finrank_adjoin_aeval_of_transcendental

set_option autoImplicit false

open Polynomial
theorem IntermediateField.finrank_adjoin_aeval_of_transcendental
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (s : L) (hs : Transcendental K s) (hgen : IntermediateField.adjoin K ({s} : Set L) = ⊤)
    (p : K[X]) (hp : 0 < p.natDegree) :
    Module.finrank ↥(IntermediateField.adjoin K ({Polynomial.aeval s p} : Set L)) L = p.natDegree := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finrank_adjoin_aeval_of_transcendental.solution
