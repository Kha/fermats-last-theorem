import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_jointly_injective
import Theorems.Thm_GaloisRepAdic_isOrdinaryAt_of_jointly_injective
import Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_jointly_injective
import P2M.Util
namespace P2MW.S_GaloisRep_ordinaryCondition_of_injective

theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (hinj : Function.Injective φ) (ρ : GaloisRepAdic A)
    {p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hnB : IsNilpotent (p : B))
    (h : GaloisRep.ordinaryCondition 𝒪 p S (ρ.baseChangeAlong φ hφ)) :
    GaloisRep.ordinaryCondition 𝒪 p S ρ := by
  have hj : ∀ x, φ x = 0 → φ x = 0 → x = 0 := fun x hx _ => hinj (by rw [hx, map_zero])
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact ⟨GaloisRepAdic.detIsCyclotomic_of_jointly_injective φ hφ φ hφ hj ρ hnB hnB h₁ h₁,
    GaloisRepAdic.isOrdinaryAt_of_jointly_injective φ hφ φ hφ hj ρ hp hp2 h₁ h₂ h₂,
    fun q hq hqS => GaloisRepAdic.isUnramifiedAt_of_jointly_injective φ hφ φ hφ hj ρ
      (h₃ q hq hqS) (h₃ q hq hqS)⟩
