import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (C : Fin k → Fin k → Type) [∀ i j, CommRing (C i j)] [∀ i j, Algebra B (C i j)] [∀ i j, Algebra 𝒪 (C i j)]
    [∀ i j, IsScalarTower 𝒪 B (C i j)] [∀ i j, IsLocalization.Away (f i * f j) (C i j)]
    [∀ i j, Algebra (Localization.Away (f i)) (C i j)] [∀ i j, Algebra (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower 𝒪 (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j)]
    (Q₂ : ∀ i j : Fin k, DrinfeldDatum (K := K) π (C i j))
    (Wl : ∀ i j : Fin k, (Q i).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) (Q₂ i j))
    (Wr : ∀ i j : Fin k, (Q j).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j))
    [∀ i, Module B (Q i).T₀] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₀]
    [∀ i, Module B (Q i).T₁] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₁] :
    ∃ (T₀ T₁ : Type) (_ : AddCommGroup T₀) (_ : AddCommGroup T₁) (_ : Module B T₀) (_ : Module B T₁)
      (_ : Module.Invertible B T₀) (_ : Module.Invertible B T₁)
      (Pi₀ : T₀ →ₗ[B] T₁) (Pi₁ : T₁ →ₗ[B] T₀) (p₀ : ∀ i, T₀ →ₗ[B] (Q i).T₀) (p₁ : ∀ i, T₁ →ₗ[B] (Q i).T₁),
      (∀ t, Pi₁ (Pi₀ t) = algebraMap 𝒪 B π • t) ∧ (∀ t, Pi₀ (Pi₁ t) = algebraMap 𝒪 B π • t) ∧
      (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i)) ∧
      (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i)) ∧
      (∀ i t, p₁ i (Pi₀ t) = (Q i).Pi₀ (p₀ i t)) ∧ (∀ i t, p₀ i (Pi₁ t) = (Q i).Pi₁ (p₁ i t)) ∧
      (∀ i j t, (Wl i j).τ₀ (p₀ i t) = (Wr i j).τ₀ (p₀ j t)) ∧
      (∀ i j t, (Wl i j).τ₁ (p₁ i t) = (Wr i j).τ₁ (p₁ j t)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap.solution
