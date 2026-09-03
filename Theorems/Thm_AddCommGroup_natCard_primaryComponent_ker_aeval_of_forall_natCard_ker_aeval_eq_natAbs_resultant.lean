import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_natCard_primaryComponent_ker_aeval_of_forall_natCard_ker_aeval_eq_natAbs_resultant

set_option autoImplicit false

theorem AddCommGroup.natCard_primaryComponent_ker_aeval_of_forall_natCard_ker_aeval_eq_natAbs_resultant
    {M : Type*} [AddCommGroup M] (T : M →+ M) (P : Polynomial ℤ) (hP : P.Monic)
    (R : Type*) [CommRing R] [IsDomain R]
    (h : ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : R) ≠ 0 →
        (G.resultant P ≠ 0 →
          Nat.card (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker =
            (G.resultant P).natAbs) ∧
        (G.resultant P = 0 →
          ¬ Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker))
    (G : Polynomial ℤ) (hG : G.Monic) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : R) ≠ 0) :
    (G.resultant P ≠ 0 →
      Nat.card (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker ℓ) =
        ℓ ^ ((G.resultant P).natAbs.factorization ℓ)) ∧
    (G.resultant P = 0 →
      ¬ Finite (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_natCard_primaryComponent_ker_aeval_of_forall_natCard_ker_aeval_eq_natAbs_resultant.solution
