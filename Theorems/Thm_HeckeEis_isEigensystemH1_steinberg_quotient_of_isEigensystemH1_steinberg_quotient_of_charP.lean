import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_HeckeEis_isEigensystemH1_steinberg_quotient_of_isEigensystemH1_steinberg_quotient_of_charP
attribute [-instance] ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

set_option autoImplicit false
open CongruenceSubgroup Polynomial

theorem
HeckeEis.isEigensystemH1_steinberg_quotient_of_isEigensystemH1_steinberg_quotient_of_charP
    {q : ℕ} [Fact q.Prime] (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S₀ : Set ℕ) (hq : q ∈ S₀) (b : ℕ → ℤ)
    (κ₀ : Type) [Field κ₀] [CharP κ₀ p]
    {V₀ : Type} [AddCommGroup V₀] [Module κ₀ V₀] [FiniteDimensional κ₀ V₀]
      (ρ₀ : Representation κ₀ (CuspidalType.GL2 q) V₀)
    (π₀ : ↥(CuspidalType.steinberg q κ₀).toSubmodule →ₗ[κ₀] V₀)
    (hπ₀ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ₀).toSubmodule,
        π₀ ⟨CuspidalType.ind q κ₀ g v, (CuspidalType.steinberg q κ₀).apply_mem_toSubmodule g v.2⟩ = ρ₀ g (π₀ v))
    (hπ₀surj : Function.Surjective π₀)
    (hπ₀ker : ∀ v : ↥(CuspidalType.steinberg q κ₀).toSubmodule,
        π₀ v = 0 ↔ ∃ c : κ₀, (v : CuspidalType.ProjLine q →₀ κ₀) = c • CuspidalType.constFun q κ₀)
    (h₀ : HeckeEis.IsEigensystemH1 N (ρ₀.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
        (fun ℓ : ℕ =>
          if h : ((ℓ : ZMod q) ≠ 0) then ρ₀ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
        S₀ (fun ℓ => ((b ℓ : ℤ) : κ₀)))
    (κ : Type) [Field κ] [CharP κ p]
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)
:
      HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
        (fun ℓ : ℕ =>
          if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
        S₀ (fun ℓ => ((b ℓ : ℤ) : κ)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEigensystemH1_steinberg_quotient_of_isEigensystemH1_steinberg_quotient_of_charP.solution
