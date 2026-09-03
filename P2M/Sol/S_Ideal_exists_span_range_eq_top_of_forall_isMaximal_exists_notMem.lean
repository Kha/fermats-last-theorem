import Mathlib
import P2M.Util
namespace P2MW.S_Ideal_exists_span_range_eq_top_of_forall_isMaximal_exists_notMem

set_option autoImplicit false

theorem solution
    {B : Type} [CommRing B] (P : B → Prop)
    (h : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ s : B, s ∉ 𝔪 ∧ P s) :
    ∃ (n : ℕ) (g : Fin n → B), Ideal.span (Set.range g) = ⊤ ∧ ∀ i : Fin n, P (g i) := by
  classical

  have htop : Ideal.span {s : B | P s} = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hs, hPs⟩ := h 𝔪 h𝔪
    exact hs (hle (Ideal.subset_span hPs))

  have h1 : (1 : B) ∈ Ideal.span {s : B | P s} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨T, hT, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1

  let e := T.equivFin
  refine ⟨T.card, fun i => (e.symm i).1, ?_, fun i => hT (e.symm i).2⟩
  rw [Ideal.eq_top_iff_one]
  refine Submodule.span_mono ?_ h1T
  intro s hs
  exact ⟨e ⟨s, hs⟩, by simp⟩
