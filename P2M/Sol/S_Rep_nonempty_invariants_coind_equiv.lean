import Mathlib
import P2M.Util
namespace P2MW.S_Rep_nonempty_invariants_coind_equiv

set_option autoImplicit false
open CategoryTheory

set_option maxHeartbeats 3200000 in

theorem solution {k G : Type} [CommRing k] [Group G] (H : Subgroup G) (N : Rep.{0} k ↥H) :
    Nonempty ((Rep.coind H.subtype N).ρ.invariants ≃ₗ[k] N.ρ.invariants) := by

  have hact : ∀ (g x : G) (f : (Rep.coind H.subtype N)), ((Rep.coind H.subtype N).ρ g f : G → N) x = (f : G → N) (x * g) :=
    fun _ _ _ => rfl

  have hconst : ∀ f : (Rep.coind H.subtype N).ρ.invariants, ∀ x : G, ((f : Rep.coind H.subtype N) : G → N) x
      = ((f : Rep.coind H.subtype N) : G → N) 1 := by
    intro f x
    have := congrArg (fun φ : Rep.coind H.subtype N => (φ : G → N) 1) (f.2 x)
    simpa [hact] using this

  have hval : ∀ f : (Rep.coind H.subtype N).ρ.invariants, ((f : Rep.coind H.subtype N) : G → N) 1 ∈ N.ρ.invariants := by
    intro f s
    have h1 := (Representation.mem_coindV H.subtype N.ρ _).1 (f : Rep.coind H.subtype N).2 s 1
    rw [mul_one] at h1
    rw [← h1]
    exact hconst f _

  have hmem : ∀ n : N.ρ.invariants, (fun _ : G => (n : N)) ∈ Representation.coindV H.subtype N.ρ := by
    intro n
    rw [Representation.mem_coindV]
    intro s _
    exact (n.2 s).symm
  have hinv : ∀ n : N.ρ.invariants, (⟨fun _ : G => (n : N), hmem n⟩ : Rep.coind H.subtype N) ∈ (Rep.coind H.subtype N).ρ.invariants := by
    intro n g
    apply Subtype.ext
    funext x
    rw [hact]
  refine ⟨{ toFun := fun f => ⟨((f : Rep.coind H.subtype N) : G → N) 1, hval f⟩
            invFun := fun n => ⟨⟨fun _ : G => (n : N), hmem n⟩, hinv n⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            left_inv := fun f => ?_
            right_inv := fun _ => rfl }⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact (hconst f x).symm
