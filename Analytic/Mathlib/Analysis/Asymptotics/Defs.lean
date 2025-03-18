import Mathlib.Analysis.Asymptotics.Defs

open Set Topology Filter NNReal

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {E''' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedAddGroup E''']
  [SeminormedRing R']

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜']
variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variable {f' : α → E'} {g' : α → F'} {k' : α → G'}
variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}
variable {l l' : Filter α}
variable {f₁ f₂ : α → E'} {g₁ g₂ : α → F'}

-- https://github.com/leanprover-community/mathlib4/pull/23059

theorem IsBigO.add_iff_left (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₁ =O[l] g):=
  ⟨fun h ↦ h.sub h₂ |>.congr (fun _ ↦ add_sub_cancel_right _ _) (fun _ ↦ rfl), fun h ↦ h.add h₂⟩

theorem IsBigO.add_iff_right (h₁ : f₁ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₂ =O[l] g):=
  ⟨fun h ↦ h.sub h₁ |>.congr (fun _ ↦ (eq_sub_of_add_eq' rfl).symm) (fun _ ↦ rfl), fun h ↦ h₁.add h⟩

theorem IsLittleO.add_iff_left (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₁ =o[l] g):=
  ⟨fun h ↦ h.sub h₂ |>.congr (fun _ ↦ add_sub_cancel_right _ _) (fun _ ↦ rfl), fun h ↦ h.add h₂⟩

theorem IsLittleO.add_iff_right (h₁ : f₁ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₂ =o[l] g):=
  ⟨fun h ↦ h.sub h₁ |>.congr (fun _ ↦ (eq_sub_of_add_eq' rfl).symm) (fun _ ↦ rfl), fun h ↦ h₁.add h⟩

theorem IsBigO.sub_iff_left (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₁ =O[l] g):=
  ⟨fun h ↦ h.add h₂ |>.congr (fun _ ↦ sub_add_cancel ..) (fun _ ↦ rfl), fun h ↦ h.sub h₂⟩

theorem IsBigO.sub_iff_right (h₁ : f₁ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₂ =O[l] g):=
  ⟨fun h ↦ h₁.sub h |>.congr (fun _ ↦ sub_sub_self ..) (fun _ ↦ rfl), fun h ↦ h₁.sub h⟩

theorem IsLittleO.sub_iff_left (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₁ =o[l] g):=
  ⟨fun h ↦ h.add h₂ |>.congr (fun _ ↦ sub_add_cancel ..) (fun _ ↦ rfl), fun h ↦ h.sub h₂⟩

theorem IsLittleO.sub_iff_right (h₁ : f₁ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₂ =o[l] g):=
  ⟨fun h ↦ h₁.sub h |>.congr (fun _ ↦ sub_sub_self ..) (fun _ ↦ rfl), fun h ↦ h₁.sub h⟩
end Asymptotics
