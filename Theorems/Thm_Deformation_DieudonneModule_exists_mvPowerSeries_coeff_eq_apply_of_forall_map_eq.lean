import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq

universe v

theorem Deformation.DieudonneModule.exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq
    (p : ℕ) [Fact p.Prime] {d : ℕ}
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, Bialgebra (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v)
    (π : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] H v)
    (hπs : ∀ v, (s v : H (v + 1) →ₐ[ZMod p] H v).comp (π (v + 1)) = π v)
    (hπε : ∀ v i, Coalgebra.counit (R := ZMod p) (π v (MvPowerSeries.X i)) = 0)
    (hπinj : ∀ G : MvPowerSeries (Fin d) (ZMod p), (∀ v, π v G = 0) → G = 0)
    (hπsurjj : ∀ z : ∀ v, H v, (∀ v, s v (z (v + 1)) = z v) →
      ∃ G : MvPowerSeries (Fin d) (ZMod p), ∀ v, π v G = z v)
    (hπker : ∀ N : ℕ, ∃ v, RingHom.ker (π v) ≤
      (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N)
    (m : ∀ v, Deformation.DieudonneModule (ZMod p) p (H v))
    (hm : ∀ v, Deformation.DieudonneModule.map (ZMod p) p (s v) (m (v + 1)) = m v) :
    ∃ abar : ℕ → MvPowerSeries (Fin d) (ZMod p),
      (∀ k, MvPowerSeries.constantCoeff (abar k) = 0) ∧
      (∀ N : ℕ, ∃ k₀, ∀ k, k₀ ≤ k →
        abar k ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) ∧
      (∀ (v n : ℕ) (u : Deformation.wittHom (ZMod p) p n (H v)),
        Deformation.DieudonneModule.of (ZMod p) p (H v) n u = m v →
        ∀ (k : ℕ) (hk : k < n),
          (u : TruncatedWittVector p n (H v)).coeff ⟨n - 1 - k, by omega⟩ = π v (abar k)) ∧
      (∀ abar' : ℕ → MvPowerSeries (Fin d) (ZMod p),
        (∀ (v n : ℕ) (u : Deformation.wittHom (ZMod p) p n (H v)),
          Deformation.DieudonneModule.of (ZMod p) p (H v) n u = m v →
          ∀ (k : ℕ) (hk : k < n),
            (u : TruncatedWittVector p n (H v)).coeff ⟨n - 1 - k, by omega⟩ = π v (abar' k)) →
        abar' = abar) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq.solution
