import Mathlib
import Theorems.Thm_RingHom_denseRange_of_isAlgClosed
import P2M.Util
namespace P2MW.S_RingHom_exists_mem_forall_mem_range_of_isOpen

theorem solution {n : ℕ} {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    (σ : F →+* ℂ) {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ b ∈ U, ∀ j, b j ∈ Set.range σ := by
  have hd : Dense (Set.pi Set.univ fun _ : Fin n => Set.range σ) :=
    dense_pi Set.univ fun _ _ => σ.denseRange_of_isAlgClosed
  obtain ⟨b, hbU, hb⟩ := hd.inter_open_nonempty U hU hne
  exact ⟨b, hbU, fun j => hb j (Set.mem_univ _)⟩
