import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Grassmannian_adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

theorem Module.Grassmannian.adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)
    (Gr : Scheme.{0}) (p : Gr ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
      Module.Grassmannian A (A ⊗[R] M) k ≃
        {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (hpt : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      (pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1)
    (V : (Fin k → M) → Gr.Opens)
    (hVchart : ∀ (x : Fin k → M) (A : Type) [CommRing A] [Algebra R A]
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      Set.range (pt A N).1.base ⊆ (V x : Set Gr) ↔
        Function.Bijective fun v : Fin k → A =>
          ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i))
    (ι : Type) (g : ι → M) (hg : Submodule.span R (Set.range g) = ⊤)
    (x : Fin k → M) (S : Type) [CommRing S] [Algebra R S] (N : Module.Grassmannian S (S ⊗[R] M) k)
    [IsOpenImmersion (pt S N).1] (hN : (pt S N).1.opensRange = V x) :
    Algebra.adjoin R {s : S | ∃ (a : ι) (c : Fin k → S) (i : Fin k),
        ∑ j, c j • N.toSubmodule.mkQ ((1 : S) ⊗ₜ[R] x j) = N.toSubmodule.mkQ ((1 : S) ⊗ₜ[R] g a) ∧
          s = c i} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Module_Grassmannian_adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq.solution
