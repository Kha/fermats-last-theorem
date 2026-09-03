import Definitions.Def_SchurMultiplierTrivial
import Mathlib.Algebra.Group.Nat.Even
import P2M.Util
import P2M.Sol.S_Ihara_ker_pow_eq_one_of_stem

universe u
theorem Ihara.ker_pow_eq_one_of_stem {E G : Type u} [Group E] [Group G] (π : E →* G)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hcomm : π.ker ≤ commutator E) (K : Subgroup G) [K.Normal] (hK : K ≤ commutator G)
    (hQ : Ihara.HasTrivialSchurMultiplier (G ⧸ K)) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    {q : ℕ} (hq : Odd q) (hKq : ∀ k ∈ K, k ^ q = 1) : ∀ c ∈ π.ker, c ^ q = 1 := by p2m_exact_reverting @_root_.P2MW.S_Ihara_ker_pow_eq_one_of_stem.solution
