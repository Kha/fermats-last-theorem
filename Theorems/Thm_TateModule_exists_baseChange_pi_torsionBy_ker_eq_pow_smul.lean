import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_exists_baseChange_pi_torsionBy_ker_eq_pow_smul

set_option autoImplicit false

open TensorProduct

theorem TateModule.exists_baseChange_pi_torsionBy_ker_eq_pow_smul
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M]
    (R : Type) [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    (n : ℕ) :
    ∃ lam : R ⊗[ℤ_[p]] ↥(TateModule p M) →+
        (Fin (Module.finrank ℤ_[p] R) → ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))),
      (∀ z : R ⊗[ℤ_[p]] ↥(TateModule p M),
        lam z = 0 ↔ ∃ w : R ⊗[ℤ_[p]] ↥(TateModule p M), z = ((p : R) ^ n) • w) ∧
      ∀ (G : Type) [Monoid G] [DistribMulAction G M] (g : G) (z : R ⊗[ℤ_[p]] ↥(TateModule p M))
        (i : Fin (Module.finrank ℤ_[p] R)),
        ((lam ((TateModule.rep p M G g).baseChange R z) i :
            ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))) : M) =
          g • ((lam z i : ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))) : M) := by p2m_exact_reverting @_root_.P2MW.S_TateModule_exists_baseChange_pi_torsionBy_ker_eq_pow_smul.solution
