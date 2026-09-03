import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq

set_option autoImplicit false
open Module
theorem IsLocalRing.finrank_invariants_linHom_fieldUnits_modPow_eq
    {q : ℕ} [Fact q.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ q ∣ Fintype.card Δ)
    {F : Type*} [Field F] (hqF : (q : F) ≠ 0) (actF : Δ →* (F ≃+* F))
    (Rs : ValuationSubring F) (act : Δ →* (Rs ≃+* Rs))
    (hact : ∀ (d : Δ) (x : Rs), ((act d x : Rs) : F) = actF d (x : F))
    {e m : ℕ} (he : Ideal.span {(q : Rs)} = maximalIdeal Rs ^ e) (hem : e < m)
    (hfin : ∀ n : ℕ, (maximalIdeal Rs ^ n).toAddSubgroup.FiniteIndex)
    (hpow : (principalUnits Rs m).map (powMonoidHom q) = principalUnits Rs (m + e))
    (hnotors : ∀ u ∈ principalUnits Rs m, u ^ q = 1 → u = 1) (hidxm : (principalUnits Rs m).FiniteIndex)
    (hidxme : (principalUnits Rs (m + e)).FiniteIndex)
    (Λ : AddSubgroup Rs) [Λ.FiniteIndex] (hΛ : ∀ (d : Δ) (x : Rs), x ∈ Λ → act d x ∈ Λ)
    {VΛ : Type*} [AddCommGroup VΛ] [Module (ZMod q) VΛ] [FiniteDimensional (ZMod q) VΛ]
    (PΛ : Representation (ZMod q) Δ VΛ) (πΛ : Λ →+ VΛ) (hπΛ : Function.Surjective πΛ)
    (hkerΛ : ∀ x : Λ, πΛ x = 0 ↔ ∃ y : Λ, q • y = x)
    (hπΛΔ : ∀ (d : Δ) (x : Λ), πΛ ⟨act d x, hΛ d x x.2⟩ = PΛ d (πΛ x))
    {ι : Type*} [Fintype ι] (b : Module.Basis (Δ × ι) (ZMod q) VΛ)
    (hb : ∀ (d d' : Δ) (i : ι), PΛ d (b (d', i)) = b (d * d', i))
    {VN : Type*} [AddCommGroup VN] [Module (ZMod q) VN] [FiniteDimensional (ZMod q) VN]
    (N : Representation (ZMod q) Δ VN)

    (v : Fˣ →* Multiplicative ℤ) (hv : Function.Surjective v)
    (hvker : ∀ x : Fˣ, v x = 1 ↔ ((x : F) ∈ Rs ∧ ((x⁻¹ : Fˣ) : F) ∈ Rs))
    (hvΔ : ∀ (d : Δ) (x : Fˣ), v (Units.map ((actF d : F ≃+* F) : F →* F) x) = v x)

    {VPF : Type*} [AddCommGroup VPF] [Module (ZMod q) VPF] (PF : Representation (ZMod q) Δ VPF)
    (πF : Additive Fˣ →+ VPF) (hπF : Function.Surjective πF)
    (hkerπF : ∀ u : Fˣ, πF (Additive.ofMul u) = 0 ↔ ∃ w : Fˣ, w ^ q = u)
    (hπFΔ : ∀ (d : Δ) (u : Fˣ), πF (Additive.ofMul (Units.map ((actF d : F ≃+* F) : F →* F) u)) = PF d (πF (Additive.ofMul u)))
    {VTF : Type*} [AddCommGroup VTF] [Module (ZMod q) VTF] (TF : Representation (ZMod q) Δ VTF)
    (ιF : VTF →+ Additive Fˣ) (hιF : Function.Injective ιF)
    (hranιF : ∀ u : Fˣ, Additive.ofMul u ∈ Set.range ιF ↔ u ^ q = 1)
    (hιFΔ : ∀ (d : Δ) (w : VTF), Additive.toMul (ιF (TF d w)) = Units.map ((actF d : F ≃+* F) : F →* F) (Additive.toMul (ιF w))) :
    finrank (ZMod q) (N.linHom PF).invariants
      = Fintype.card ι * finrank (ZMod q) VN + finrank (ZMod q) (N.linHom TF).invariants
        + finrank (ZMod q) (N.linHom (Representation.trivial (ZMod q) Δ (ZMod q))).invariants := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.solution
