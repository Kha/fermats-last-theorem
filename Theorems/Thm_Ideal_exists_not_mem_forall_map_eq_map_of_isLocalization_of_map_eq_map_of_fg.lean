import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg

set_option autoImplicit false

theorem Ideal.exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg
    {S B : Type} [CommRing S] [CommRing B] (φ : S →+* B) (𝔭 : Ideal S) [𝔭.IsPrime]
    (Bₚ : Type) [CommRing Bₚ] [Algebra B Bₚ] [IsLocalization (𝔭.primeCompl.map φ.toMonoidHom) Bₚ]
    (J₁ J₂ : Ideal B) (h₁ : J₁.FG) (h₂ : J₂.FG)
    (h : J₁.map (algebraMap B Bₚ) = J₂.map (algebraMap B Bₚ)) :
    ∃ g : S, g ∉ 𝔭 ∧
      ∀ (B' : Type) [CommRing B'] [Algebra B B'] [IsLocalization.Away (φ g) B'],
        J₁.map (algebraMap B B') = J₂.map (algebraMap B B') := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg.solution
