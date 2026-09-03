import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one
    {R : Type u} [CommRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (d : ℤ)
    (hK : Subsingleton (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift σ.ker d) 1))
    (hF : ∀ c : ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift σ.F d) 0,
      ∃ f : σ.F.M, f ∈ σ.F.grade d ∧
        ∃ hf : f ∈ (ProjSpaceCech.GradedModule.shift σ.F d).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
          ∀ s : ProjSpaceCech.Idx n 0,
            (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (ProjSpaceCech.GradedModule.shift σ.F d) 0)) from c).1 s =
              ProjSpaceCech.GradedModule.sec.mk (ProjSpaceCech.GradedModule.shift σ.F d) (ProjSpaceCech.Idx.img n s)
                ⟨0, fun _ _ => rfl, f, hf⟩) :
    ∀ c : ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift D d) 0,
      ∃ m : D.M, m ∈ D.grade d ∧
        ∃ hm : m ∈ (ProjSpaceCech.GradedModule.shift D d).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
          ∀ s : ProjSpaceCech.Idx n 0,
            (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (ProjSpaceCech.GradedModule.shift D d) 0)) from c).1 s =
              ProjSpaceCech.GradedModule.sec.mk (ProjSpaceCech.GradedModule.shift D d) (ProjSpaceCech.Idx.img n s)
                ⟨0, fun _ _ => rfl, m, hm⟩ := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.solution
