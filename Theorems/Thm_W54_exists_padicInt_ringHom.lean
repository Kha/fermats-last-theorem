import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import P2M.Util
import P2M.Sol.S_W54_exists_padicInt_ringHom

theorem W54.exists_padicInt_ringHom (p : ℕ) [Fact p.Prime]
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪']
    (hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪') :
    ∃ φ : ℤ_[p] →+* 𝒪', IsLocalHom φ := by p2m_exact_reverting @_root_.P2MW.S_W54_exists_padicInt_ringHom.solution
