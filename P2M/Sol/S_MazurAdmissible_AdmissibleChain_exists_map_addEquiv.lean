import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule
import P2M.Util
namespace P2MW.S_MazurAdmissible_AdmissibleChain_exists_map_addEquiv

set_option linter.unusedSectionVars false

noncomputable section

p2m_open "MazurAdmissible P2MW.S_MazurAdmissible_AdmissibleChain_exists_map_addEquiv.MazurAdmissible"

namespace MazurAdmissible
p2m_export "MazurAdmissible" "OpenAction AdmissibleChain filtAlpha filtLength"
p2m_open "MazurAdmissible"

open Function

universe u v

namespace AdmissibleChain p2m_export "MazurAdmissible.AdmissibleChain" "tag hmono step n hact htop hbot hcard" end AdmissibleChain
p2m_open_scoped "MazurAdmissible.AdmissibleChain" in

theorem AdmissibleChain.exists_map_addEquiv_aux
    {M : Type u} [AddCommGroup M] {M' : Type v} [AddCommGroup M']
    {p : ℕ} {Φ : OpenAction M} {Φ' : OpenAction M'} (e : M ≃+ M')
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M), Φ'.φ σ (e x) = e (Φ.φ σ x))
    (c : AdmissibleChain p Φ) :
    ∃ c' : AdmissibleChain p Φ', filtAlpha c' = filtAlpha c ∧ filtLength c' = filtLength c := by
  classical
  refine ⟨{ n := c.n
            step := fun i => (c.step i).map e.toAddMonoidHom
            hbot := by rw [c.hbot, AddSubgroup.map_bot]
            htop := by
              rw [c.htop, ← AddMonoidHom.range_eq_map]
              exact AddMonoidHom.range_eq_top.mpr e.surjective
            hmono := fun i => AddSubgroup.map_mono (c.hmono i)
            tag := c.tag
            hcard := fun i => ?_
            hact := fun i => ?_ }, rfl, rfl⟩
  ·
    have h := c.hcard i
    change (c.step i.castSucc).relIndex (c.step i.succ) = p at h
    change ((c.step i.castSucc).map e.toAddMonoidHom).relIndex ((c.step i.succ).map e.toAddMonoidHom) = p
    exact (AddSubgroup.relIndex_map_map_of_injective _ _ e.injective).trans h
  · have hi := c.hact i
    split_ifs at hi ⊢ with ht
    · intro σ y hy
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
      refine AddSubgroup.mem_map.mpr ⟨Φ.φ σ x - x, hi σ x hx, ?_⟩
      change e (Φ.φ σ x - x) = Φ'.φ σ (e x) - e x
      rw [map_sub, he]
    · intro σ ζ hζ a ha y hy
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
      refine AddSubgroup.mem_map.mpr ⟨Φ.φ σ x - a • x, hi σ ζ hζ a ha x hx, ?_⟩
      change e (Φ.φ σ x - a • x) = Φ'.φ σ (e x) - a • e x
      rw [map_sub, map_nsmul, he]

end MazurAdmissible

open _root_.MazurAdmissible _root_.P2MW.S_MazurAdmissible_AdmissibleChain_exists_map_addEquiv.MazurAdmissible in
theorem solution
    {M : Type*} [AddCommGroup M] {M' : Type*} [AddCommGroup M']
    {p : ℕ} {Φ : OpenAction M} {Φ' : OpenAction M'} (e : M ≃+ M')
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M), Φ'.φ σ (e x) = e (Φ.φ σ x))
    (c : AdmissibleChain p Φ) :
    ∃ c' : AdmissibleChain p Φ', filtAlpha c' = filtAlpha c ∧ filtLength c' = filtLength c :=
  MazurAdmissible.AdmissibleChain.exists_map_addEquiv_aux e he c

end
