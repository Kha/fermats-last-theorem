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
import P2M.Sol.S_MonoidAlgebra_exists_mvPowerSeries_algHom_surjective_ker_eq

universe u v
theorem MonoidAlgebra.exists_mvPowerSeries_algHom_surjective_ker_eq {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] {p : ℕ} [Fact p.Prime] (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) {r : ℕ} (k : Fin r → ℕ) : ∃ θ : MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] MonoidAlgebra 𝒪 (Π i : Fin r, Multiplicative (ZMod (p ^ k i))), (∀ i, θ (MvPowerSeries.X i) = MonoidAlgebra.of 𝒪 _ (Pi.mulSingle i (Multiplicative.ofAdd 1)) - 1) ∧ Function.Surjective θ ∧ RingHom.ker θ = Ideal.span (Set.range fun i : Fin r => ((1 + MvPowerSeries.X i) ^ (p ^ k i) - 1 : MvPowerSeries (Fin r) 𝒪)) ∧ ∀ f, Bialgebra.counitAlgHom 𝒪 _ (θ f) = MvPowerSeries.constantCoeff f := by p2m_exact_reverting @_root_.P2MW.S_MonoidAlgebra_exists_mvPowerSeries_algHom_surjective_ker_eq.solution
