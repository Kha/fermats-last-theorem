import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Index
import P2M.Util
import P2M.Sol.S_Ihara_ker_eq_bot_of_stem_of_fibre

theorem Ihara.ker_eq_bot_of_stem_of_fibre {E G Q : Type*} [Group E] [Group G] [Group Q]
    (π : E →* G) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : π.ker ≤ commutator E) (K : Subgroup G) [K.Normal]
    (hWab : ∀ x ∈ K.comap π, ∀ y ∈ K.comap π, x * y = y * x) {q : ℕ}
    (hCq : ∀ c ∈ π.ker, c ^ q = 1) (ρ : G →* Q) (hK : ρ.ker = K) (u : G)
    [((Subgroup.zpowers (ρ u)).comap ρ).FiniteIndex]
    (hidx : Nat.Coprime ((Subgroup.zpowers (ρ u)).comap ρ).index q)
    (hcent : ∀ k ∈ K, u * k = k * u → k ∈ Subgroup.zpowers u) : π.ker = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Ihara_ker_eq_bot_of_stem_of_fibre.solution
