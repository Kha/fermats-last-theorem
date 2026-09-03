import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import P2M.Util
import P2M.Sol.S_MonoidAlgebra_ker_counitAlgHom_eq_span_of_closure_eq_top

universe u v
theorem MonoidAlgebra.ker_counitAlgHom_eq_span_of_closure_eq_top {𝒪 : Type u} [CommRing 𝒪] {G : Type v} [Group G] (S : Set G) (hS : Subgroup.closure S = ⊤) : RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)) = Ideal.span ((fun g => MonoidAlgebra.of 𝒪 G g - 1) '' S) := by p2m_exact_reverting @_root_.P2MW.S_MonoidAlgebra_ker_counitAlgHom_eq_span_of_closure_eq_top.solution
