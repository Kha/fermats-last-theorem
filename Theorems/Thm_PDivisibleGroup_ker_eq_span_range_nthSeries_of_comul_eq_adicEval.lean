import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_ker_eq_span_range_nthSeries_of_comul_eq_adicEval

open MvPowerSeries
open scoped TensorProduct

universe u v

theorem PDivisibleGroup.ker_eq_span_range_nthSeries_of_comul_eq_adicEval
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h₀ : ℕ) (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, HopfAlgebra 𝓞 (R₀ v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)] [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v) (ht₀ : ∀ v, Function.Surjective (t₀ v))
    (hrank₀ : ∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀))
    (hker₀ : ∀ v, RingHom.ker (t₀ v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (R₀ (v + 1)) (p ^ v))
    (hconn : ∀ v, IsLocalRing (R₀ v))
    (d : ℕ) (π : ∀ v, MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R₀ v)
    (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v, (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v).comp (π (v + 1)) = π v)
    (hπε : ∀ v i, Coalgebra.counit (R := 𝓞) (π v (X i)) = 0)
    (hπX : ∀ v i, π v (X i) ∈ (Ideal.span {(p : R₀ v)}).radical)
    (hπinj : ∀ G, (∀ v, π v G = 0) → G = 0)
    (hπsurjj : ∀ z : ∀ v, R₀ v, (∀ v, t₀ v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v)
    (F : MvFormalGroup d 𝓞)
    (hπΔ : ∀ v i, Coalgebra.comul (R := 𝓞) (π v (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R₀ v ⊗[𝓞] R₀ v)})
        (Sum.elim (fun j => π v (X j) ⊗ₜ[𝓞] (1 : R₀ v)) (fun j => (1 : R₀ v) ⊗ₜ[𝓞] π v (X j)))
        (F.toPowerSeries i))
    (v : ℕ) :
    RingHom.ker (π v) = Ideal.span (Set.range (F.nthSeries (p ^ v))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_ker_eq_span_range_nthSeries_of_comul_eq_adicEval.solution
