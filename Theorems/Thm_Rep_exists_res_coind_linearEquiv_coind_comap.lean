import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_res_coind_linearEquiv_coind_comap

set_option autoImplicit false

universe u v w w'

open CategoryTheory

theorem Rep.exists_res_coind_linearEquiv_coind_comap
    {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]
    {Γ : Type w} {G : Type w'} [Group Γ] [Group G] (r : G →* Γ) (U : Subgroup Γ) [U.Normal]
    (γ : Γ ⧸ (U ⊔ r.range) → Γ) (hγ : ∀ t, (γ t : Γ ⧸ (U ⊔ r.range)) = t) :
    ∃ e : Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V)) ≃ₗ[k]
        Rep.coind (U.comap r).subtype (Rep.trivial k ↥(U.comap r) (Γ ⧸ (U ⊔ r.range) → V)),
      (∀ (g : G) (f : Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))),
        e ((Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))).ρ g f) =
          (Rep.coind (U.comap r).subtype (Rep.trivial k ↥(U.comap r) (Γ ⧸ (U ⊔ r.range) → V))).ρ g (e f)) ∧
      ∀ (f : Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))) (h : G) (t : Γ ⧸ (U ⊔ r.range)),
        ((e f : Rep.coind (U.comap r).subtype (Rep.trivial k ↥(U.comap r) (Γ ⧸ (U ⊔ r.range) → V))) :
            G → (Γ ⧸ (U ⊔ r.range) → V)) h t =
          (f : Γ → V) (γ t * r h) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_res_coind_linearEquiv_coind_comap.solution
