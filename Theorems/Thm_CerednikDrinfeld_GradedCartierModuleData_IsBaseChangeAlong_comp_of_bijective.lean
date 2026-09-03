import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_comp_of_bijective

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong.comp_of_bijective
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B'] (j : CerednikDrinfeld.Zp2 p →+* B)
    (φ : B →+* B')
    (D₁ : CerednikDrinfeld.GradedCartierModuleData p B j)
    (D₂ D₃ : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j))
    (f : D₁.M →+ D₂.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D₁ D₂ f)
    (g : D₂.M →+ D₃.M) (hg : Function.Bijective g)
    (hW : ∀ (w : WittVector p B') (x : D₂.M), g (w • x) = w • g x)
    (hF : ∀ x, g (D₂.frobenius x) = D₃.frobenius (g x))
    (hV : ∀ x, g (D₂.verschiebung x) = D₃.verschiebung (g x))
    (hPi : ∀ x, g (D₂.varpi x) = D₃.varpi (g x))
    (hpc : ∀ (i : Fin 2) (x : D₂.M), x ∈ D₂.piece i → g x ∈ D₃.piece i) :
    CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D₁ D₃ (g.comp f) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_comp_of_bijective.solution
