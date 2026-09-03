import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_cartierDual_pow_apply_tmul_eq_algebraMap_constantCoeff_iterate

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem MvFormalGroup.cartierDual_pow_apply_tmul_eq_algebraMap_constantCoeff_iterate
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞)
    (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    (i : Fin d) (D : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))
    (hDi : ∀ j, D ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = if i = j then 1 else 0)
    (hDii : ∀ a b : ZMod p ⊗[𝓞] R, D (a * b) =
      D a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * D b)
    (L : MvPowerSeries (Fin d) 𝓞 → MvPowerSeries (Fin d) 𝓞)
    (hL : ∀ (H : MvPowerSeries (Fin d) 𝓞) (a : Fin d →₀ ℕ),
      (L H).coeff a = (subst F.toPowerSeries H).coeff (a.sumElim (Finsupp.single i 1)))
    (n : ℕ) (H : MvPowerSeries (Fin d) 𝓞) :
    (D ^ n) ((1 : ZMod p) ⊗ₜ[𝓞] π H) = algebraMap 𝓞 (ZMod p) ((L^[n] H).constantCoeff) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_cartierDual_pow_apply_tmul_eq_algebraMap_constantCoeff_iterate.solution
