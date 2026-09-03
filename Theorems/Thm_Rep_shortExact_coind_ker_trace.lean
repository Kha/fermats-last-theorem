import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_shortExact_coind_ker_trace
set_option autoImplicit false
universe u
open CategoryTheory
theorem Rep.shortExact_coind_ker_trace {k G : Type u} [Field k] [Group G]
    (U : Subgroup G) [U.FiniteIndex]
    {A B C : Rep.{u} k G} (α : A ⟶ B) (β : B ⟶ C)
    (hα : Function.Injective α.hom) (hβ : Function.Surjective β.hom) (hex : ∀ b : B, β.hom b = 0 ↔ ∃ a : A, α.hom a = b)
    (τA : Rep.coind U.subtype (Rep.res U.subtype A) ⟶ A) (τB : Rep.coind U.subtype (Rep.res U.subtype B) ⟶ B) (τC : Rep.coind U.subtype (Rep.res U.subtype C) ⟶ C)
    (hτA : ∀ y : Rep.coind U.subtype (Rep.res U.subtype A), τA.hom y = ∑ᶠ c : G ⧸ U, A.ρ c.out ((y : G → A) (c.out)⁻¹))
    (hτB : ∀ y : Rep.coind U.subtype (Rep.res U.subtype B), τB.hom y = ∑ᶠ c : G ⧸ U, B.ρ c.out ((y : G → B) (c.out)⁻¹))
    (hτC : ∀ y : Rep.coind U.subtype (Rep.res U.subtype C), τC.hom y = ∑ᶠ c : G ⧸ U, C.ρ c.out ((y : G → C) (c.out)⁻¹))
    {KA KB KC : Rep.{u} k G} (iA : KA ⟶ Rep.coind U.subtype (Rep.res U.subtype A)) (iB : KB ⟶ Rep.coind U.subtype (Rep.res U.subtype B)) (iC : KC ⟶ Rep.coind U.subtype (Rep.res U.subtype C))
    (hiA : Function.Injective iA.hom) (hτiA : ∀ y : Rep.coind U.subtype (Rep.res U.subtype A), τA.hom y = 0 ↔ ∃ κ : KA, iA.hom κ = y)
    (hiB : Function.Injective iB.hom) (hτiB : ∀ y : Rep.coind U.subtype (Rep.res U.subtype B), τB.hom y = 0 ↔ ∃ κ : KB, iB.hom κ = y)
    (hiC : Function.Injective iC.hom) (hτiC : ∀ y : Rep.coind U.subtype (Rep.res U.subtype C), τC.hom y = 0 ↔ ∃ κ : KC, iC.hom κ = y)
    (Yα : Rep.coind U.subtype (Rep.res U.subtype A) ⟶ Rep.coind U.subtype (Rep.res U.subtype B)) (Yβ : Rep.coind U.subtype (Rep.res U.subtype B) ⟶ Rep.coind U.subtype (Rep.res U.subtype C))
    (hYα : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype A)) (g : G), ((Yα.hom y : Rep.coind U.subtype (Rep.res U.subtype B)) : G → B) g = α.hom ((y : G → A) g))
    (hYβ : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype B)) (g : G), ((Yβ.hom y : Rep.coind U.subtype (Rep.res U.subtype C)) : G → C) g = β.hom ((y : G → B) g))
    (Kα : KA ⟶ KB) (Kβ : KB ⟶ KC) (hKα : Kα ≫ iB = iA ≫ Yα) (hKβ : Kβ ≫ iC = iB ≫ Yβ) :
    (Function.Injective Yα.hom ∧ Function.Surjective Yβ.hom ∧ ∀ y : Rep.coind U.subtype (Rep.res U.subtype B), Yβ.hom y = 0 ↔ ∃ x : Rep.coind U.subtype (Rep.res U.subtype A), Yα.hom x = y) ∧
    (Function.Injective Kα.hom ∧ Function.Surjective Kβ.hom ∧ ∀ y : KB, Kβ.hom y = 0 ↔ ∃ x : KA, Kα.hom x = y) := by p2m_exact_reverting @_root_.P2MW.S_Rep_shortExact_coind_ker_trace.solution
