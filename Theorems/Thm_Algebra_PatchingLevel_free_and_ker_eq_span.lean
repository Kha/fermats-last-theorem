import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import P2M.Util
import P2M.Sol.S_Algebra_PatchingLevel_free_and_ker_eq_span

theorem Algebra.PatchingLevel.free_and_ker_eq_span
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Nontrivial M]
    (L : Algebra.PatchingLevel 𝒪 r R M ⊥) :
    Module.Free R M ∧ Module.annihilator R M = ⊥ ∧
      RingHom.ker L.ψ = Ideal.span (Set.range fun i : Fin r => L.φ (MvPowerSeries.X i)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_PatchingLevel_free_and_ker_eq_span.solution
