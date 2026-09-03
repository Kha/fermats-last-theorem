import Mathlib
import P2M.Util
import P2M.Sol.S_AdjoinRoot_exists_algHom_equiv_subtype_eval_map_eq_zero_natural

set_option autoImplicit false

universe u v w

open Polynomial

theorem AdjoinRoot.exists_algHom_equiv_subtype_eval_map_eq_zero_natural
    {Λ : Type u} [CommRing Λ] (S : Type v) [CommRing S] [Algebra Λ S] (g : S[X]) :
    ∃ η : ∀ (T : Type w) [CommRing T] [Algebra Λ T],
        ((AdjoinRoot g →ₐ[Λ] T) ≃ {p : (S →ₐ[Λ] T) × T // (g.map (p.1 : S →+* T)).eval p.2 = 0}),
      (∀ (T : Type w) [CommRing T] [Algebra Λ T] (φ : AdjoinRoot g →ₐ[Λ] T),
        ((η T φ).1 : (S →ₐ[Λ] T) × T) =
          (φ.comp (IsScalarTower.toAlgHom Λ S (AdjoinRoot g)), φ (AdjoinRoot.root g))) ∧
      ∀ (T : Type w) [CommRing T] [Algebra Λ T] (T' : Type w) [CommRing T'] [Algebra Λ T']
        (f : T →ₐ[Λ] T') (φ : AdjoinRoot g →ₐ[Λ] T),
        ((η T' (f.comp φ)).1 : (S →ₐ[Λ] T') × T') = (f.comp (η T φ).1.1, f (η T φ).1.2) := by p2m_exact_reverting @_root_.P2MW.S_AdjoinRoot_exists_algHom_equiv_subtype_eval_map_eq_zero_natural.solution
