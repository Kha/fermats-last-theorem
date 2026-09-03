import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsLocalRing_finrank_invariants_linHom_units_modPow_eq

set_option autoImplicit false
open Module
theorem IsLocalRing.finrank_invariants_linHom_units_modPow_eq
    {q : ℕ} [Fact q.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ q ∣ Fintype.card Δ)
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] (hqR : (q : R) ≠ 0)
    (act : Δ →* (R ≃+* R))
    {e m : ℕ} (he : Ideal.span {(q : R)} = maximalIdeal R ^ e) (hem : e < m)
    (hfin : ∀ n : ℕ, (maximalIdeal R ^ n).toAddSubgroup.FiniteIndex)
    (hpow : (principalUnits R m).map (powMonoidHom q) = principalUnits R (m + e))
    (hnotors : ∀ u ∈ principalUnits R m, u ^ q = 1 → u = 1) (hidxm : (principalUnits R m).FiniteIndex)
    (hidxme : (principalUnits R (m + e)).FiniteIndex)
    (Λ : AddSubgroup R) [Λ.FiniteIndex] (hΛ : ∀ (d : Δ) (x : R), x ∈ Λ → act d x ∈ Λ)
    {VΛ : Type*} [AddCommGroup VΛ] [Module (ZMod q) VΛ] [FiniteDimensional (ZMod q) VΛ]
    (PΛ : Representation (ZMod q) Δ VΛ) (πΛ : Λ →+ VΛ) (hπΛ : Function.Surjective πΛ)
    (hkerΛ : ∀ x : Λ, πΛ x = 0 ↔ ∃ y : Λ, q • y = x)
    (hπΛΔ : ∀ (d : Δ) (x : Λ), πΛ ⟨act d x, hΛ d x x.2⟩ = PΛ d (πΛ x))
    {ι : Type*} [Fintype ι] (b : Module.Basis (Δ × ι) (ZMod q) VΛ)
    (hb : ∀ (d d' : Δ) (i : ι), PΛ d (b (d', i)) = b (d * d', i))
    {VN : Type*} [AddCommGroup VN] [Module (ZMod q) VN] [FiniteDimensional (ZMod q) VN]
    (N : Representation (ZMod q) Δ VN)

    {VP : Type*} [AddCommGroup VP] [Module (ZMod q) VP] [FiniteDimensional (ZMod q) VP]
    (P : Representation (ZMod q) Δ VP)
    (π : Additive Rˣ →+ VP) (hπ : Function.Surjective π)
    (hkerπ : ∀ u : Rˣ, π (Additive.ofMul u) = 0 ↔ ∃ v : Rˣ, v ^ q = u)
    (hπΔ : ∀ (d : Δ) (u : Rˣ), π (Additive.ofMul (Units.map ((act d : R ≃+* R) : R →* R) u)) = P d (π (Additive.ofMul u)))

    {VT : Type*} [AddCommGroup VT] [Module (ZMod q) VT] [FiniteDimensional (ZMod q) VT]
    (T : Representation (ZMod q) Δ VT)
    (ιT : VT →+ Additive Rˣ) (hιT : Function.Injective ιT)
    (hranιT : ∀ u : Rˣ, Additive.ofMul u ∈ Set.range ιT ↔ u ^ q = 1)
    (hιTΔ : ∀ (d : Δ) (w : VT), Additive.toMul (ιT (T d w)) = Units.map ((act d : R ≃+* R) : R →* R) (Additive.toMul (ιT w))) :
    finrank (ZMod q) (N.linHom P).invariants
      = Fintype.card ι * finrank (ZMod q) VN + finrank (ZMod q) (N.linHom T).invariants := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_finrank_invariants_linHom_units_modPow_eq.solution
