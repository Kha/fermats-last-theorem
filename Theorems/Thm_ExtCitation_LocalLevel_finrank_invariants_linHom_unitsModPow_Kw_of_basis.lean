import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_Kw_of_basis

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open Module
theorem ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_Kw_of_basis
    (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ q ∣ Fintype.card Δ) (act : Δ →* (Kw ≃ₐ[ℚ_[q]] Kw))
    {ι : Type*} [Fintype ι] (w : Δ × ι → Kw) (hwR : ∀ x, w x ∈ Rw q Kw) (hw : LinearIndependent ℚ_[q] w)
    (hcard : Fintype.card (Δ × ι) = Module.finrank ℚ_[q] Kw)
    (hperm : ∀ (d d' : Δ) (i : ι), act d (w (d', i)) = w (d * d', i))
    {VN : Type*} [AddCommGroup VN] [Module (ZMod q) VN] [FiniteDimensional (ZMod q) VN]
    (N : Representation (ZMod q) Δ VN)
    {VPF : Type*} [AddCommGroup VPF] [Module (ZMod q) VPF] (PF : Representation (ZMod q) Δ VPF)
    (πF : Additive (↥Kw)ˣ →+ VPF) (hπF : Function.Surjective πF)
    (hkerπF : ∀ u : (↥Kw)ˣ, πF (Additive.ofMul u) = 0 ↔ ∃ w : (↥Kw)ˣ, w ^ q = u)
    (hπFΔ : ∀ (d : Δ) (u : (↥Kw)ˣ),
      πF (Additive.ofMul (Units.map (act d : Kw →* Kw) u)) = PF d (πF (Additive.ofMul u)))
    {VTF : Type*} [AddCommGroup VTF] [Module (ZMod q) VTF] (TF : Representation (ZMod q) Δ VTF)
    (ιF : VTF →+ Additive (↥Kw)ˣ) (hιF : Function.Injective ιF)
    (hranιF : ∀ u : (↥Kw)ˣ, Additive.ofMul u ∈ Set.range ιF ↔ u ^ q = 1)
    (hιFΔ : ∀ (d : Δ) (v : VTF),
      Additive.toMul (ιF (TF d v)) = Units.map (act d : Kw →* Kw) (Additive.toMul (ιF v))) :
    finrank (ZMod q) (N.linHom PF).invariants
      = Fintype.card ι * finrank (ZMod q) VN + finrank (ZMod q) (N.linHom TF).invariants
        + finrank (ZMod q) (N.linHom (Representation.trivial (ZMod q) Δ (ZMod q))).invariants := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_Kw_of_basis.solution
