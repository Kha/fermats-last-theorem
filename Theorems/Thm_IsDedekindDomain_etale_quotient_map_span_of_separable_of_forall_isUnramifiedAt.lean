import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt

set_option autoImplicit false

open Polynomial TensorProduct

universe u

theorem IsDedekindDomain.etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt
    {k : Type u} [Field k] (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]
    (h : k[X]) (hsep : h.Separable)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ → Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
      Algebra.IsUnramifiedAt k[X] P) :
    Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt.solution
