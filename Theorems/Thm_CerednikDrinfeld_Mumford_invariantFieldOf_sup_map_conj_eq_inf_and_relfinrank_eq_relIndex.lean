import Mathlib.FieldTheory.Relrank
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_invariantFieldOf_sup_map_conj_eq_inf_and_relfinrank_eq_relIndex

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.invariantFieldOf_sup_map_conj_eq_inf_and_relfinrank_eq_relIndex
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]
    (Γ : Subgroup G) (s : G)
    (N : Subgroup G) (hN : N ≤ Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom)
    (hNΓ : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N)
    (hfin : N.relIndex Γ ≠ 0)
    (hF1 : ∀ γ ∈ Γ, (∀ x ∈ invariantFieldOf K G M N, γ • x = x) → γ ∈ N)
    (hF2 : ∀ γ ∈ Γ, (∀ x ∈ invariantFieldOf K G M Γ, (s⁻¹ * γ * s) • x = x) → s⁻¹ * γ * s ∈ Γ) :
    invariantFieldOf K G M Γ ⊔ invariantFieldOf K G M (Γ.map (MulAut.conj s).toMonoidHom) =
        invariantFieldOf K G M (Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom) ∧
      Subfield.relfinrank (invariantFieldOf K G M Γ) (invariantFieldOf K G M (Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom)) =
        (Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom).relIndex Γ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_invariantFieldOf_sup_map_conj_eq_inf_and_relfinrank_eq_relIndex.solution
