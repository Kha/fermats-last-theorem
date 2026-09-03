import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_filtration_binaryForm_subquotient_le_sub_one

set_option autoImplicit false

theorem HeckeEis.exists_filtration_binaryForm_subquotient_le_sub_one (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (n : ℕ) :
    ∃ (r : ℕ) (W : Fin (r + 1) → Submodule K ↥(HeckeEis.BinaryForm K n)),
      W 0 = ⊥ ∧ W (Fin.last r) = ⊤ ∧ Monotone W ∧
      (∀ (i : Fin (r + 1)) (M : Matrix (Fin 2) (Fin 2) ℤ), ¬ (p : ℤ) ∣ M.det →
        Submodule.map (HeckeEis.binaryFormRep K n M) (W i) ≤ W i) ∧
      ∀ i : Fin r, ∃ (a b : ℕ) (π : ↥(HeckeEis.BinaryForm K n) →ₗ[K] ↥(HeckeEis.BinaryForm K a)),
        a ≤ p - 1 ∧ Submodule.map π (W i.succ) = ⊤ ∧ W i.castSucc = W i.succ ⊓ LinearMap.ker π ∧
        ∀ (M : Matrix (Fin 2) (Fin 2) ℤ), ¬ (p : ℤ) ∣ M.det → ∀ w ∈ W i.succ,
          π (HeckeEis.binaryFormRep K n M w)
            = (((M.det : ℤ) : K) ^ b) • HeckeEis.binaryFormRep K a M (π w) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_filtration_binaryForm_subquotient_le_sub_one.solution
