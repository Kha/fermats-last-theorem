import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing

set_option autoImplicit false

theorem RingHom.existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing
    (R A C : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing C]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]
    (hinj : Function.Injective (algebraMap R A))
    (hinv : ∀ a : A, (∀ g : G, g • a = a) → a ∈ Set.range (algebraMap R A))
    (π : R)
    (c : ∀ n : ℕ, C →+* A ⧸ Ideal.span {algebraMap R A π ^ n})
    (hc : ∀ n : ℕ, (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap R A π) (Nat.le_succ n)))).comp (c (n + 1)) = c n)
    (hG : ∀ (n : ℕ) (g : G) (z : C) (a : A), Ideal.Quotient.mk _ a = c n z →
        Ideal.Quotient.mk (Ideal.span {algebraMap R A π ^ n}) (g • a) = c n z) :
    ∃! d : ∀ n : ℕ, C →+* R ⧸ Ideal.span {π ^ n},
      (∀ n : ℕ, (Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ n)))).comp (d (n + 1)) = d n) ∧
      (∀ n : ℕ, (Ideal.quotientMap (Ideal.span {algebraMap R A π ^ n}) (algebraMap R A)
          (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← map_pow]; exact Ideal.subset_span rfl)).comp (d n) = c n) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing.solution
