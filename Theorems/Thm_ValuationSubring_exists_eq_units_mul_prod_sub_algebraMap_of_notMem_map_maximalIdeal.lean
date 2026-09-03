import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal

set_option autoImplicit false

open IsLocalRing

universe u

theorem ValuationSubring.exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal
    {L : Type u} [Field L] [IsAlgClosed L] (A : ValuationSubring L) [HenselianLocalRing ↥A]
    {S : Type u} [CommRing S] [IsLocalRing S] [Algebra ↥A S] [IsLocalHom (algebraMap ↥A S)]
    [Algebra.EssFiniteType ↥A S]
    (hres : Function.Surjective (algebraMap ↥A (ResidueField S)))
    (t : S) (ht : maximalIdeal S = Ideal.span {t} ⊔ (maximalIdeal ↥A).map (algebraMap ↥A S))
    (hprime : ((maximalIdeal ↥A).map (algebraMap ↥A S)).IsPrime)
    (h : S) (hh : h ∉ (maximalIdeal ↥A).map (algebraMap ↥A S)) :
    ∃ (n : ℕ) (u : Sˣ) (r : Fin n → ↥A), (∀ i, r i ∈ maximalIdeal ↥A) ∧
      h = (u : S) * ∏ i, (t - algebraMap ↥A S (r i)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal.solution
