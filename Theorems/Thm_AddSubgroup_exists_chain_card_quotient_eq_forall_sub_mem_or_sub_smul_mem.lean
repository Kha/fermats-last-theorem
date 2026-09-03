import Mathlib
import P2M.Util
import P2M.Sol.S_AddSubgroup_exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem
import Definitions.Def_Compat_Mathlib430

theorem AddSubgroup.exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem
    {Γ M : Type*} [Group Γ] [AddCommGroup M] (φ : Γ →* AddAut M) {q : ℕ} (hq : q.Prime)
    (χ : Γ →* (ZMod q)ˣ) (A B : AddSubgroup M) (hAB : A ≤ B)
    (hfin : Finite (↥B ⧸ A.addSubgroupOf B))
    (hA : ∀ g : Γ, ∀ x ∈ A, φ g x ∈ A) (hB : ∀ g : Γ, ∀ x ∈ B, φ g x ∈ B)
    (hqB : ∀ x ∈ B, q • x ∈ A)
    (h : ∀ g : Γ, ∀ x ∈ B,
      φ g (φ g x - (χ g : ZMod q).val • x) - (φ g x - (χ g : ZMod q).val • x) ∈ A) :
    ∃ (n : ℕ) (step : Fin (n + 1) → AddSubgroup M), step 0 = A ∧ step (Fin.last n) = B ∧
      ∀ i : Fin n, step i.castSucc ≤ step i.succ ∧
        Nat.card (↥(step i.succ) ⧸ (step i.castSucc).addSubgroupOf (step i.succ)) = q ∧
        ((∀ g : Γ, ∀ x ∈ step i.succ, φ g x - x ∈ step i.castSucc) ∨
         (∀ g : Γ, ∀ x ∈ step i.succ, φ g x - (χ g : ZMod q).val • x ∈ step i.castSucc)) := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem.solution
