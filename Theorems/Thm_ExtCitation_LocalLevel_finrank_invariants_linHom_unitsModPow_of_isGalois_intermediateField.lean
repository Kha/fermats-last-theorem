import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open Module
theorem ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (Kw : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K Kw] [IsGalois K Kw]
    (htame : ¬ p ∣ Module.finrank K Kw)
    {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
    (N : Representation (ZMod p) (Kw ≃ₐ[K] Kw) VN)
    {VPF : Type*} [AddCommGroup VPF] [Module (ZMod p) VPF] (PF : Representation (ZMod p) (Kw ≃ₐ[K] Kw) VPF)
    (πF : Additive (↥Kw)ˣ →+ VPF) (hπF : Function.Surjective πF)
    (hkerπF : ∀ u : (↥Kw)ˣ, πF (Additive.ofMul u) = 0 ↔ ∃ w : (↥Kw)ˣ, w ^ p = u)
    (hπFΔ : ∀ (σ : Kw ≃ₐ[K] Kw) (u : (↥Kw)ˣ),
      πF (Additive.ofMul (Units.map (σ : Kw →* Kw) u)) = PF σ (πF (Additive.ofMul u)))
    {VTF : Type*} [AddCommGroup VTF] [Module (ZMod p) VTF] (TF : Representation (ZMod p) (Kw ≃ₐ[K] Kw) VTF)
    (ιF : VTF →+ Additive (↥Kw)ˣ) (hιF : Function.Injective ιF)
    (hranιF : ∀ u : (↥Kw)ˣ, Additive.ofMul u ∈ Set.range ιF ↔ u ^ p = 1)
    (hιFΔ : ∀ (σ : Kw ≃ₐ[K] Kw) (v : VTF),
      Additive.toMul (ιF (TF σ v)) = Units.map (σ : Kw →* Kw) (Additive.toMul (ιF v))) :
    finrank (ZMod p) (N.linHom PF).invariants
      = Module.finrank ℚ_[p] K * finrank (ZMod p) VN + finrank (ZMod p) (N.linHom TF).invariants
        + finrank (ZMod p) (N.linHom (Representation.trivial (ZMod p) (Kw ≃ₐ[K] Kw) (ZMod p))).invariants := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField.solution
