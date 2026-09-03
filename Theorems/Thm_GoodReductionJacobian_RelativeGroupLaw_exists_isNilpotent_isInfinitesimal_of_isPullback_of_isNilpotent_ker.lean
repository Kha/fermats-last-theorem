import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField
theorem GoodReductionJacobian.RelativeGroupLaw.exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker
    (q : ℕ) (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of B)) (L : RelativeGroupLaw B f)
    {A₀ : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)) (L₀ : RelativeGroupLaw B₀ f₀)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (hgmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ g =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hinf₀ : ∀ (C : Type) [CommRing C] [Algebra B₀ C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B₀) C) f₀),
      nsmulPt L₀ (Scheme.specOver (𝒪 := B₀) C) (q ^ m) P = L₀.one (Scheme.specOver (𝒪 := B₀) C) →
        ∃ J : Ideal C, IsNilpotent J ∧ L₀.IsInfinitesimal J P)
    (C : Type) [CommRing C] [Algebra B C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B) C) f)
    (hP : nsmulPt L (Scheme.specOver (𝒪 := B) C) (q ^ m) P = L.one (Scheme.specOver (𝒪 := B) C)) :
    ∃ J : Ideal C, IsNilpotent J ∧ L.IsInfinitesimal J P := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker.solution
