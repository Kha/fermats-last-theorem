import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_place_residue_eq_algebraMap_of_maximalIdeal_eq_span_sup

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.exists_place_residue_eq_algebraMap_of_maximalIdeal_eq_span_sup
    {k : Type} [Field k] {Fbar : Type} [Field Fbar] [Algebra k Fbar]
    {F : Type} [Field F]
    (B : ValuationSubring F) (res : ↥B →+* Fbar) (hres : Function.Surjective res)
    (hker : RingHom.ker res = maximalIdeal ↥B)
    (S : Subring F) (hSB : ∀ f : ↥S, (f : F) ∈ B) (hS : IsLocalRing ↥S)
    (χ₀ : ↥S →+* k) (hχ₀ : RingHom.ker χ₀ = maximalIdeal ↥S)
    (hconst : ∀ c : k, ∃ a : ↥S, χ₀ a = c ∧ res ⟨(a : F), hSB a⟩ = algebraMap k Fbar c)
    (𝔮 : Ideal ↥S) (h𝔮 : ∀ f : ↥S, f ∈ 𝔮 ↔ (⟨(f : F), hSB f⟩ : ↥B) ∈ maximalIdeal ↥B)
    (t : ↥S) (hmax : maximalIdeal ↥S = Ideal.span {t} ⊔ 𝔮) (hne : 𝔮 ≠ maximalIdeal ↥S)
    (hnoeth : IsNoetherianRing (↥S ⧸ 𝔮))
    (hfrac : ∀ b : ↥B, ∃ g h : ↥S, h ∉ 𝔮 ∧ (b : F) * (h : F) = (g : F)) :
    ∃ Q : Place k Fbar, Q.IsRational ∧
      (∀ Q' : Place k Fbar, (∀ f : ↥S, res ⟨(f : F), hSB f⟩ ∈ Q'.toValuationSubring) → Q' = Q) ∧
      (∀ f : ↥S, ∃ hm : res ⟨(f : F), hSB f⟩ ∈ Q.toValuationSubring,
        IsLocalRing.residue ↥Q.toValuationSubring ⟨res ⟨(f : F), hSB f⟩, hm⟩ =
          algebraMap k Q.ResidueField (χ₀ f)) ∧
      Q.ord (res ⟨(t : F), hSB t⟩) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_place_residue_eq_algebraMap_of_maximalIdeal_eq_span_sup.solution
