import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem MvFormalGroup.exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (n : ℕ)
    [Module.Free 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (Φ.nthSeries n)))]
    [Module.Finite 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (Φ.nthSeries n)))]
    (hnil : ∀ i : Fin d, ∃ N : ℕ, (MvPowerSeries.X i : MvPowerSeries (Fin d) 𝓞) ^ N ∈
      Ideal.span (Set.range (Φ.nthSeries n)) ⊔ Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)}) :
    ∃ (L : Type u) (_ : CommRing L) (_ : HopfAlgebra 𝓞 L) (_ : Coalgebra.IsCocomm 𝓞 L)
      (_ : Module.Free 𝓞 L) (_ : Module.Finite 𝓞 L) (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L),
      Function.Surjective π ∧
      RingHom.ker π = Ideal.span (Set.range (Φ.nthSeries n)) ∧
      (∀ i, π (MvPowerSeries.X i) ∈ (Ideal.span {(p : L)}).radical) ∧
      (∀ G, π G = MvFormalGroup.adicEval (Ideal.span {(p : L)}) (fun i => π (MvPowerSeries.X i)) G) ∧
      (∀ i, Coalgebra.comul (R := 𝓞) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)})
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[𝓞] (1 : L))
            (fun j => (1 : L) ⊗ₜ[𝓞] π (MvPowerSeries.X j)))
          (Φ.toPowerSeries i)) ∧
      (∀ G, Coalgebra.counit (R := 𝓞) (π G) = MvPowerSeries.constantCoeff G) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete.solution
