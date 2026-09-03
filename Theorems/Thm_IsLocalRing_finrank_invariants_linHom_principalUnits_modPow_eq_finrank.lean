import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank

set_option autoImplicit false
open Module
theorem IsLocalRing.finrank_invariants_linHom_principalUnits_modPow_eq_finrank
    {q : ℕ} [Fact q.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ q ∣ Fintype.card Δ)
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] (hqR : (q : R) ≠ 0)
    (act : Δ →* (R ≃+* R))
    {e m : ℕ} (he : Ideal.span {(q : R)} = maximalIdeal R ^ e) (hem : e < m)
    (hfin : ∀ n : ℕ, (maximalIdeal R ^ n).toAddSubgroup.FiniteIndex)
    (hpow : (principalUnits R m).map (powMonoidHom q) = principalUnits R (m + e))
    (Λ : AddSubgroup R) [Λ.FiniteIndex] (hΛ : ∀ (d : Δ) (x : R), x ∈ Λ → act d x ∈ Λ)
    {VΛ : Type*} [AddCommGroup VΛ] [Module (ZMod q) VΛ] [FiniteDimensional (ZMod q) VΛ]
    (PΛ : Representation (ZMod q) Δ VΛ) (πΛ : Λ →+ VΛ) (hπΛ : Function.Surjective πΛ)
    (hkerΛ : ∀ x : Λ, πΛ x = 0 ↔ ∃ y : Λ, q • y = x)
    (hπΛΔ : ∀ (d : Δ) (x : Λ), πΛ ⟨act d x, hΛ d x x.2⟩ = PΛ d (πΛ x))
    {ι : Type*} [Fintype ι] (b : Module.Basis (Δ × ι) (ZMod q) VΛ)
    (hb : ∀ (d d' : Δ) (i : ι), PΛ d (b (d', i)) = b (d * d', i))
    {VN : Type*} [AddCommGroup VN] [Module (ZMod q) VN] [FiniteDimensional (ZMod q) VN]
    (N : Representation (ZMod q) Δ VN)
    {VU : Type*} [AddCommGroup VU] [Module (ZMod q) VU] (PU : Representation (ZMod q) Δ VU)
    (πU : Additive (principalUnits R m) →+ VU) (hπU : Function.Surjective πU)
    (hkerU : ∀ u : principalUnits R m,
      πU (Additive.ofMul u) = 0 ↔ ∃ v : principalUnits R m, v ^ q = u)
    (hπUΔ : ∀ (d : Δ) (u : principalUnits R m) (hu : Units.map ((act d : R ≃+* R) : R →* R) (u : Rˣ) ∈ principalUnits R m),
      πU (Additive.ofMul ⟨Units.map ((act d : R ≃+* R) : R →* R) u, hu⟩) = PU d (πU (Additive.ofMul u))) :
    finrank (ZMod q) (N.linHom PU).invariants = Fintype.card ι * finrank (ZMod q) VN := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.solution
