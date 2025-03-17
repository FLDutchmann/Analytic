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

theorem IsBigO.add_iff (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₁ =O[l] g):= by
  constructor
  · intro h
    convert h.sub h₂ with x
    abel
  · intro h
    exact h.add h₂

theorem IsBigO.sub_iff (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₁ =O[l] g):= by
  constructor
  · intro h
    convert h₂.add h with x
    abel
  · intro h
    exact h.sub h₂

end Asymptotics
