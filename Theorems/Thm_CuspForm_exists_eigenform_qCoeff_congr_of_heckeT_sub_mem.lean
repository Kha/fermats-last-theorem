import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_exists_eigenform_qCoeff_congr_of_heckeT_sub_mem
set_option autoImplicit false
open CuspForm ModularFormClass

theorem CuspForm.exists_eigenform_qCoeff_congr_of_heckeT_sub_mem (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (w : ℤ) (S : Set ℕ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) w) (hFK : ∀ n : ℕ, qCoeff F n ∈ K)
    (hFint : ∀ n : ℕ, ∃ x : integralClosure ℤ ℂ, (x : ℂ) = qCoeff F n)
    (hFne : ∃ (n : ℕ) (x : integralClosure ℤ ℂ), (x : ℂ) = qCoeff F n ∧ x ∉ 𝔪)
    (cT : ℕ → ℤ) (cU : ℤ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) (n : ℕ) (x x' : integralClosure ℤ ℂ),
      (x : ℂ) = qCoeff (heckeTLin w hℓ hℓM F) n → (x' : ℂ) = qCoeff F n → x - cT ℓ * x' ∈ 𝔪)
    (hU : ∀ (n : ℕ) (x x' : integralClosure ℤ ℂ),
      (x : ℂ) = qCoeff (heckeULin w hpM F) n → (x' : ℂ) = qCoeff F n → x - cU * x' ∈ 𝔪) :
    ∃ 𝔪' : Ideal (integralClosure ℤ ℂ), 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 M) w,
      (∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪' ∧ (x : ℂ) = y * qCoeff f n) ∧
      (∃ (n : ℕ) (x y : integralClosure ℤ ℂ), y ∉ 𝔪' ∧ (x : ℂ) = y * qCoeff f n ∧ x ∉ 𝔪') ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
        ∃ lam : integralClosure ℤ ℂ, lam - cT ℓ ∈ 𝔪' ∧ heckeTLin w hℓ hℓM f = (lam : ℂ) • f) ∧
      (∃ α : integralClosure ℤ ℂ, α - cU ∈ 𝔪' ∧ heckeULin w hpM f = (α : ℂ) • f) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_eigenform_qCoeff_congr_of_heckeT_sub_mem.solution
