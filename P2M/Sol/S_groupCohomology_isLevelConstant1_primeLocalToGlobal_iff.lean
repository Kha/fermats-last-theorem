import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import P2M.Util
namespace P2MW.S_groupCohomology_isLevelConstant1_primeLocalToGlobal_iff

set_option autoImplicit false
open ExtCitation groupCohomology
open Polynomial
open scoped Pointwise

theorem solution
    (q : Nat.Primes) [Fact (q : ℕ).Prime] {X : Type*}
    (f : primeLocalGaloisGroup q → X) :
    IsLevelConstant₁ (primeLocalToGlobal q) f ↔
      ∃ K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)), FiniteDimensional ℚ_[(q : ℕ)] K ∧
        ∀ g s : primeLocalGaloisGroup q, s ∈ K.fixingSubgroup → f (g * s) = f g :=
  exists_finiteDimensional_comap_localGaloisToGlobal_iff (q : ℕ)
    (fun U => ∀ g s : primeLocalGaloisGroup q, s ∈ U → f (g * s) = f g)
    (fun _ _ hVU h g s hs => h g s (hVU hs))
