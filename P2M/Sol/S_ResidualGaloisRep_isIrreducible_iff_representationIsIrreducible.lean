import Definitions.Def_GaloisRep_Residual
import Mathlib.RepresentationTheory.Irreducible
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_isIrreducible_iff_representationIsIrreducible

theorem solution {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    ρ.IsIrreducible ↔ Representation.IsIrreducible ρ.ρ := by
  have hV : Nontrivial ρ.V :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [ρ.finrank_eq]; exact Nat.two_pos)
  have hinj := Subrepresentation.toSubmodule_injective (ρ := ρ.ρ)
  have hbot : (⊥ : Subrepresentation ρ.ρ).toSubmodule = ⊥ := rfl
  have htop : (⊤ : Subrepresentation ρ.ρ).toSubmodule = ⊤ := rfl
  constructor
  · intro h
    have hnt : Nontrivial (Subrepresentation ρ.ρ) :=
      ⟨⟨⊥, ⊤, fun e => bot_ne_top (hbot ▸ htop ▸ congrArg Subrepresentation.toSubmodule e)⟩⟩
    exact { toNontrivial := hnt
            eq_bot_or_eq_top := fun S =>
              (h S.toSubmodule fun σ x hx => S.apply_mem_toSubmodule σ hx).imp
                (fun e => hinj (e.trans hbot.symm)) (fun e => hinj (e.trans htop.symm)) }
  · intro h W hW
    have hS := h.eq_bot_or_eq_top ⟨W, fun σ v hv => hW σ v hv⟩
    exact hS.imp (fun e => (congrArg Subrepresentation.toSubmodule e).trans hbot)
      (fun e => (congrArg Subrepresentation.toSubmodule e).trans htop)
