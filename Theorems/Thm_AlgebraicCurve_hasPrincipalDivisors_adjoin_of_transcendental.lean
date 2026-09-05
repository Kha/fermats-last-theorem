module

public import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental

@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_adjoin_of_transcendental (K : Type*) [Field K] [CharZero K] {LF : Type*} [Field LF] [Algebra K LF]
    (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral (IntermediateField.adjoin K ({x} : Set LF)) t) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.solution
