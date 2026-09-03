import Mathlib
import Theorems.Thm_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes
import P2M.Util
namespace P2MW.S_IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes

theorem solution
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {x : A} (hx : x ≠ 0) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ associatedPrimes A (A ⧸ Ideal.span {x})) : P ∈ (Ideal.span {x}).minimalPrimes := by
  have h1 : P.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hx P hP
  have hle : Ideal.span {x} ≤ P := by
    have h := (show IsAssociatedPrime P (A ⧸ Ideal.span {x}) from hP).annihilator_le
    rwa [Submodule.annihilator_top, Ideal.annihilator_quotient] at h

  have hbelow : ∀ q : Ideal A, q.IsPrime → q < P → q = ⊥ := by
    intro q hq hlt
    haveI := hq
    have hPle : P.height ≤ ((1 : ℕ) : ℕ∞) := by rw [h1]; norm_cast
    have hlt1 : q.height < ((1 : ℕ) : ℕ∞) := (Ideal.height_le_iff.mp hPle) q hq hlt
    have h0 : q.height = 0 := by
      apply ENat.lt_one_iff_eq_zero.mp
      exact_mod_cast hlt1
    have hmin : q ∈ (⊥ : Ideal A).minimalPrimes := Ideal.height_eq_zero_iff.mp h0
    simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hmin
  refine ⟨⟨‹P.IsPrime›, hle⟩, fun q hq hqP => ?_⟩
  rcases lt_or_eq_of_le hqP with hlt | rfl
  · exfalso
    have hqbot := hbelow q hq.1 hlt
    apply hx
    have hxq : x ∈ q := hq.2 (Ideal.subset_span rfl)
    simpa [hqbot] using hxq
  · exact le_rfl
