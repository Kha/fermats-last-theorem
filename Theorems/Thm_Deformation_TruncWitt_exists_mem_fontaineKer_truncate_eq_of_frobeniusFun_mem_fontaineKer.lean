import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import P2M.Util
import P2M.Sol.S_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer

universe u v w

theorem Deformation.TruncWitt.exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer
    {ℛ : Type u} [CommRing ℛ] (p : ℕ) [Fact p.Prime]
    {A : Type v} [CommRing A] (π : ℛ →+* A) (hπ : Function.Surjective π)
    (hker : RingHom.ker π ≤ Ideal.span {(p : ℛ)})
    {n : ℕ} {u : TruncatedWittVector p n A}
    (hu : Deformation.TruncWitt.frobeniusFun u ∈ Deformation.TruncWitt.fontaineKer p n π) :
    ∃ b : TruncatedWittVector p (n + 1) A,
      b ∈ Deformation.TruncWitt.fontaineKer p (n + 1) π ∧
      TruncatedWittVector.truncate (Nat.le_succ n) b = u := by p2m_exact_reverting @_root_.P2MW.S_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer.solution
