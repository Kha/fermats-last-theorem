import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_IsPullbackVia_comp

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM

theorem solution
    {r N : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] {B'' : Type} [CommRing B''] [Algebra 𝒪 B'']
    (φ : B →ₐ[𝒪] B') (φ' : B' →ₐ[𝒪] B'') {ψ : Onr →ₐ[𝒪] B}
    {E : FakeEllipticCurve Λ N B} {E' : FakeEllipticCurve Λ N B'} {E'' : FakeEllipticCurve Λ N B''}
    (g : E'.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E E' g)
    (g' : E''.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia (φ' : B' →+* B'') E' E'' g')
    (hgg : FakeEllipticCurve.IsPullbackVia ((φ'.comp φ : B →ₐ[𝒪] B'') : B →+* B'') E E'' (g' ≫ g))
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) E')
    (ρ'' : FakeEllipticCurve.Rigidification r π A₀ (φ'.comp (φ.comp ψ)) E'')
    (h : FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ρ ρ')
    (h' : FakeEllipticCurve.Rigidification.IsPullbackVia φ' g' hg' ρ' ρ'') :
    FakeEllipticCurve.Rigidification.IsPullbackVia (φ'.comp φ) (g' ≫ g) hgg ρ ρ'' := by
  obtain ⟨ub, uA, hub, hubg, huA, huAg, hd, hsq⟩ := h
  obtain ⟨ub', uA', hub', hub'g, huA', huA'g, hd', hsq'⟩ := h'
  have hq : ∀ (I : Ideal B) (I' : Ideal B') (I'' : Ideal B'') (h₁ : I ≤ I'.comap (φ : B →+* B')) (h₂ : I' ≤ I''.comap (φ' : B' →+* B''))
      (h₃ : I ≤ I''.comap ((φ'.comp φ : B →ₐ[𝒪] B'') : B →+* B'')),
      Ideal.quotientMap I'' ((φ'.comp φ : B →ₐ[𝒪] B'') : B →+* B'') h₃ = (Ideal.quotientMap I'' (φ' : B' →+* B'') h₂).comp (Ideal.quotientMap I' (φ : B →+* B') h₁) := by
    intro I I' I'' h₁ h₂ h₃
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl
  refine ⟨ub' ≫ ub, uA' ≫ uA, ?_, ?_, ?_, ?_, hd'.trans hd, ?_⟩
  · have hc := CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp _ _ ρ.Eb ρ'.Eb ρ''.Eb ub ub' hub hub'
    rw [← hq] at hc
    exact hc
  · rw [Category.assoc, hubg, ← Category.assoc, hub'g, Category.assoc]
  · have hc := CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp _ _ ρ.Ab ρ'.Ab ρ''.Ab uA uA' huA huA'
    rw [← hq] at hc
    exact hc
  · rw [Category.assoc, huAg, huA'g]
  · rw [Category.assoc, hsq, ← Category.assoc, hsq', Category.assoc]
