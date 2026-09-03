import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false
open Module CategoryTheory groupCohomology
theorem groupCohomology.finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K]
    (hKG : ∀ (g : Ω ≃ₐ[k] Ω) (x : Ω), x ∈ K → g x ∈ K)
    {p : ℕ} [Fact p.Prime] (χ : (Ω ≃ₐ[k] Ω) →* (ZMod p)ˣ) {ζ : Ωˣ} (hζp : IsPrimitiveRoot ζ p)
    (hζ : ∀ g : Ω ≃ₐ[k] Ω, g • ζ = ζ ^ (χ g : ZMod p).val) (hζK : (ζ : Ω) ∈ K)
    (hroots : ∀ a : Ω, a ∈ K → a ≠ 0 → ∃ α : Ω, α ^ p = a)
    (A : Rep.{0} (ZMod p) (Ω ≃ₐ[k] Ω)) [FiniteDimensional (ZMod p) A]
    (htriv : ∀ s ∈ K.fixingSubgroup, ∀ v : A, A.ρ s v = v)
    (W : Submodule (ZMod p) (cocycles₁ (Rep.res K.fixingSubgroup.subtype A)))
    (hW : ∀ c, c ∈ W ↔
      (∃ E : IntermediateField k Ω, FiniteDimensional k E ∧
        ∀ (g s : K.fixingSubgroup), (s : Ω ≃ₐ[k] Ω) ∈ E.fixingSubgroup → c (g * s) = c g) ∧
      ∀ (g : Ω ≃ₐ[k] Ω) (s t : K.fixingSubgroup), (g⁻¹ * s * g : Ω ≃ₐ[k] Ω) = t → A.ρ g (c t) = c s)
    {VX : Type} [AddCommGroup VX] [Module (ZMod p) VX] (X : Representation (ZMod p) (Ω ≃ₐ[k] Ω) VX)
    (π : (↥K)ˣ → VX) (hπmul : ∀ a b, π (a * b) = π a + π b) (hπsurj : Function.Surjective π)
    (hπker : ∀ a : (↥K)ˣ, π a = 0 ↔ ∃ b : (↥K)ˣ, b ^ p = a)
    (hπG : ∀ (g : Ω ≃ₐ[k] Ω) (a b : (↥K)ˣ), g ((a : K) : Ω) = ((b : K) : Ω) → X g (π a) = π b) :
    finrank (ZMod p) W = finrank (ZMod p) ((A.dualTwist χ).ρ.linHom X).invariants := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist.solution
