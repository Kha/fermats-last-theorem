import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_etale_isIdempotentElem_finite_away_forall_liesOver_notMem

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Algebra.exists_etale_isIdempotentElem_finite_away_forall_liesOver_notMem
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S]
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (e : R' ⊗[R] S) (_ : IsIdempotentElem e),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      Module.Finite R' (Localization.Away e) ∧
      ∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P → e ∉ P'' := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_etale_isIdempotentElem_finite_away_forall_liesOver_notMem.solution
