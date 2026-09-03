import Definitions.Def_Algebra_PatchingDatum
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_Algebra_nonempty_patchingDatum_of_levelData

theorem Algebra.nonempty_patchingDatum_of_levelData {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] {p : ℕ} [Fact p.Prime] (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (r : ℕ) (R : Type) [CommRing R] [Algebra 𝒪 R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ → Fin r → ℕ) (hk : ∀ n i, n ≤ k n i) (Rn : ℕ → Type) [∀ n, CommRing (Rn n)] [∀ n, Algebra 𝒪 (Rn n)] [∀ n, IsLocalRing (Rn n)] [∀ n, IsNoetherianRing (Rn n)] (γ : ∀ n, MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] Rn n) (hγ : ∀ n, Function.Surjective (γ n)) (ι : ∀ n, MonoidAlgebra 𝒪 (Π i : Fin r, Multiplicative (ZMod (p ^ k n i))) →ₐ[𝒪] Rn n) (ε : ∀ n, Rn n →ₐ[𝒪] R) (hε : ∀ n, Function.Surjective (ε n)) (hει : ∀ n (g : Π i : Fin r, Multiplicative (ZMod (p ^ k n i))), ε n (ι n (MonoidAlgebra.of 𝒪 _ g)) = 1) (Mn : ℕ → Type) [∀ n, AddCommGroup (Mn n)] [∀ n, Module (Rn n) (Mn n)] (d : ℕ → ℕ) (b : ∀ n, Fin (d n) → Mn n) (hspan : ∀ n (x : Mn n), ∃ c : Fin (d n) → MonoidAlgebra 𝒪 (Π i : Fin r, Multiplicative (ZMod (p ^ k n i))), x = ∑ i, ι n (c i) • b n i) (hrel : ∀ n (c : Fin (d n) → MonoidAlgebra 𝒪 (Π i : Fin r, Multiplicative (ZMod (p ^ k n i)))), ∑ i, ι n (c i) • b n i = 0 ↔ ∀ i, c i = 0) (lam : ∀ n, Mn n →+ M) (hlam_smul : ∀ n (x : Rn n) (m : Mn n), lam n (x • m) = ε n x • lam n m) (hlam_surj : ∀ n, Function.Surjective (lam n)) (hlam_ker : ∀ n (m : Mn n), lam n m = 0 ↔ m ∈ (Ideal.map (ι n) (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 (Π i : Fin r, Multiplicative (ZMod (p ^ k n i))))))) • (⊤ : Submodule (Rn n) (Mn n))) : Nonempty (Algebra.PatchingDatum 𝒪 p r R M) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_nonempty_patchingDatum_of_levelData.solution
