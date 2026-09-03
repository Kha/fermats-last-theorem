import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_cartierDual_apply_tmul_eq_and_map_mul_of_ker_eq_span_nthSeries

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem MvFormalGroup.exists_cartierDual_apply_tmul_eq_and_map_mul_of_ker_eq_span_nthSeries
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (v : ℕ) (hv : 0 < v)
    (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    :
    ∃ D : Fin d → CartierDual (ZMod p) (ZMod p ⊗[𝓞] R),
      (∀ i j, D i ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = if i = j then 1 else 0) ∧
      (∀ i (a b : ZMod p ⊗[𝓞] R), D i (a * b) =
        D i a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * D i b) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_cartierDual_apply_tmul_eq_and_map_mul_of_ker_eq_span_nthSeries.solution
