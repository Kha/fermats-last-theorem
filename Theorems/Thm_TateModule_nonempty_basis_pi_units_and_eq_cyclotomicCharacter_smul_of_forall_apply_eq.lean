import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq

set_option autoImplicit false

theorem TateModule.nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [∀ i : ℕ, HasEnoughRootsOfUnity L (p ^ i)]
    (ι : Type) [Finite ι] :
    Nonempty (Module.Basis ι ℤ_[p] (TateModule p (ι → Additive Lˣ))) ∧
    ∀ (σ : L ≃+* L) (s t : TateModule p (ι → Additive Lˣ)),
      (∀ (v : ℕ) (i : ι), ((Additive.toMul ((s : ℕ → ι → Additive Lˣ) v i) : Lˣ) : L) =
          σ (((Additive.toMul ((t : ℕ → ι → Additive Lˣ) v i) : Lˣ) : L))) →
      s = ((cyclotomicCharacter L p σ : ℤ_[p]ˣ) : ℤ_[p]) • t := by p2m_exact_reverting @_root_.P2MW.S_TateModule_nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq.solution
