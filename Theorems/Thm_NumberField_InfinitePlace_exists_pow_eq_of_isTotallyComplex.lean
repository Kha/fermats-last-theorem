import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlace_exists_pow_eq_of_isTotallyComplex
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem NumberField.InfinitePlace.exists_pow_eq_of_isTotallyComplex
    (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (w : InfinitePlace K) (u : (w.Completion)ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ v : (w.Completion)ˣ, v ^ n = u := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlace_exists_pow_eq_of_isTotallyComplex.solution
