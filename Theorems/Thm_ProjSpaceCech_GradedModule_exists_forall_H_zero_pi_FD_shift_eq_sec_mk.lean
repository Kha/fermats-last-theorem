import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.exists_forall_H_zero_pi_FD_shift_eq_sec_mk
    (R : Type u) [CommRing R] (n : ℕ) {ι : Type} [Fintype ι] (e : ι → ℤ) :
    ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d →
      ∀ c : ProjSpaceCech.GradedModule.H
          (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d) 0,
        ∃ f : (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)).M,
          f ∈ (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)).grade d ∧
          ∃ hf : f ∈ (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d).grade
              (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
            ∀ s : ProjSpaceCech.Idx n 0,
              (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d
                  (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d) 0))
                from c).1 s =
                ProjSpaceCech.GradedModule.sec.mk
                  (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d)
                  (ProjSpaceCech.Idx.img n s) ⟨0, fun _ _ => rfl, f, hf⟩ := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.solution
