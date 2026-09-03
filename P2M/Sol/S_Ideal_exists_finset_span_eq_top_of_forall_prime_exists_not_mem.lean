import Mathlib
import P2M.Util
namespace P2MW.S_Ideal_exists_finset_span_eq_top_of_forall_prime_exists_not_mem

set_option autoImplicit false

theorem solution
    {S : Type} [CommRing S] (P : S → Prop)
    (h : ∀ 𝔭 : PrimeSpectrum S, ∃ g : S, g ∉ 𝔭.asIdeal ∧ P g) :
    ∃ (k : ℕ) (g : Fin k → S), Ideal.span (Set.range g) = ⊤ ∧ ∀ i, P (g i) := by
  classical

  have htop : Ideal.span {g : S | P g} = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hg, hPg⟩ := h ⟨𝔪, h𝔪.isPrime⟩
    exact hg (hle (Ideal.subset_span hPg))

  have h1 : (1 : S) ∈ Ideal.span {g : S | P g} := by rw [htop]; trivial
  obtain ⟨T, hT, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  obtain ⟨k, e⟩ : ∃ k : ℕ, Nonempty (Fin k ≃ ↥T) :=
    ⟨T.card, ⟨(Finset.equivFin T).symm⟩⟩
  obtain ⟨e⟩ := e
  refine ⟨k, fun i => (e i : S), ?_, fun i => hT (e i).2⟩
  rw [Ideal.eq_top_iff_one, show Set.range (fun i : Fin k => ((e i : ↥T) : S)) = (T : Set S) from ?_]
  · exact h1T
  · ext x
    constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩
