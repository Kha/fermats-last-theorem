import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval

set_option autoImplicit false

theorem TateModule.charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval
    (p : ℕ) [Fact p.Prime] {M : Type} [AddCommGroup M] (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (α : M →+ M) (P : Polynomial ℤ) (hP : P.Monic)
    (hker : ∀ G : Polynomial ℤ, G.Monic → G.resultant P ≠ 0 →
      Nat.card (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) α.toIntLinearMap G).toAddMonoidHom.ker p) =
        p ^ ((G.resultant P).natAbs.factorization p))
    (hker0 : ∀ G : Polynomial ℤ, G.Monic → G.resultant P = 0 →
      ¬ Finite (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) α.toIntLinearMap G).toAddMonoidHom.ker p))
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M)) :
    (LinearMap.toMatrix b b (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).charpoly =
      P.map (Int.castRingHom ℤ_[p]) := by p2m_exact_reverting @_root_.P2MW.S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval.solution
