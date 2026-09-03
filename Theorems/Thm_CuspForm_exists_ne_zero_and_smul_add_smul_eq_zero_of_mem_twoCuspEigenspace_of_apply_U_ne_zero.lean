import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import P2M.Util
import P2M.Sol.S_CuspForm_exists_ne_zero_and_smul_add_smul_eq_zero_of_mem_twoCuspEigenspace_of_apply_U_ne_zero

set_option autoImplicit false

theorem CuspForm.exists_ne_zero_and_smul_add_smul_eq_zero_of_mem_twoCuspEigenspace_of_apply_U_ne_zero
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : Subring ℂ) (π : A) (hmax : (Ideal.span ({π} : Set A)).IsMaximal)
    (hp : (p : A) ∈ Ideal.span ({π} : Set A))
    (χ : CohCarrier.Gen M (∅ : Set ℕ) → A ⧸ Ideal.span ({π} : Set A))
    (hord : χ (CohCarrier.Gen.U p Fact.out hpM) ≠ 0)
    (ω₁ ω₂ : CuspForm.TwoCuspForms M H 2 p A (Ideal.span ({π} : Set A)))
    (h₁ : ω₁ ∈ CuspForm.twoCuspEigenspace (Ideal.span ({π} : Set A)) ∅ χ)
    (h₂ : ω₂ ∈ CuspForm.twoCuspEigenspace (Ideal.span ({π} : Set A)) ∅ χ) :
    ∃ c : (A ⧸ Ideal.span ({π} : Set A)) × (A ⧸ Ideal.span ({π} : Set A)),
      c ≠ 0 ∧ c.1 • ω₁ + c.2 • ω₂ = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_ne_zero_and_smul_add_smul_eq_zero_of_mem_twoCuspEigenspace_of_apply_U_ne_zero.solution
