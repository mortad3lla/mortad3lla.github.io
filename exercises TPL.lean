-- EXERCISES OF THE BOOK THEOREM PROVING IN LEAN 4 --
section CHAPTER3


variable (p q r : Prop)

#check Iff.intro
#check And.intro
#check Or.intro_left
#check Or.elim

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (show (p ∧ q → q ∧ p) from fun (h : p ∧ q) => And.intro (h.right) (h.left))
    (show (q ∧ p → p ∧ q) from fun (h : q ∧ p) => And.intro (h.right) (h.left))


example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun (h : p ∨ q) => Or.elim (h) (fun (hp : p) => Or.intro_right q hp) (fun (hq : q) => Or.intro_left p hq))
    (fun (h : q ∨ p) => Or.elim (h) (fun (hq : q) => Or.intro_right p hq) (fun (hp : p) => Or.intro_left q hp))


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun (h : (p ∧ q) ∧ r) =>
        And.intro ((h.left).left) (And.intro ((h.left).right) (h.right))
        )
    (fun (h : (p ∧ (q ∧ r))) =>
        And.intro (And.intro (h.left) ((h.right).left)) ((h.right).right)
    )


#check Iff.intro
#check Or.elim
#check Or.intro_left

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro

    (show (p ∨ q) ∨ r → p ∨ (q ∨ r) from
      fun (h : (p ∨ q) ∨ r) => Or.elim h
        (fun (hpq : p ∨ q) => Or.elim hpq
          (fun (hp : p) => Or.intro_left (q ∨ r) hp)
          (fun (hq : q) => Or.intro_right p (Or.intro_left r hq)))
        (fun (hr : r) => Or.intro_right p (Or.intro_right q hr)))

    (show p ∨ (q ∨ r) → (p ∨ q) ∨ r from
      fun (h : p ∨ (q ∨ r)) => Or.elim h
        (fun (hp : p) => Or.intro_left (r) (Or.intro_left q hp))
        (fun (hqr : q ∨ r) => Or.elim hqr
          (fun (hq : q) => Or.intro_left r (Or.intro_right p hq))
          (fun (hr : r) => Or.intro_right (p ∨ q) hr) ))


#check Iff.intro
#check Or.elim
#check Or.intro_left
#check And.intro

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun (h : p ∧ (q ∨ r)) =>
      Or.elim
      (h.right)
      (fun (hq : q) =>
        Or.intro_left
        (p ∧ r)
        ⟨h.left, hq⟩)
      (fun (hr : r) =>
        Or.intro_right
        (p ∧ q)
        ⟨h.left, hr⟩ )
      )
    (fun (h : (p ∧ q) ∨ (p ∧ r)) =>
      Or.elim
      h
      (fun (hpq : p ∧ q) =>
        ⟨hpq.left, (Or.intro_left r hpq.right)⟩)
      (fun (hpr : p ∧ r) =>
        ⟨hpr.left, (Or.intro_right q hpr.right)⟩)
      )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (fun (h : p ∨ (q ∧ r)) =>
    Or.elim
    h
    (fun (hp : p) =>
      And.intro
      (Or.intro_left q hp)
      (Or.intro_left r hp))
    (fun (hqr : q ∧ r) =>
      And.intro
      (Or.intro_right p hqr.left)
      (Or.intro_right p hqr.right))
    )
  (fun (h : (p ∨ q) ∧ (p ∨ r)) =>
    Or.elim
    h.left
    (fun (hp : p) =>
      Or.intro_left (q ∧ r) hp)
    (fun (hq : q) =>
      Or.elim
      h.right
      (fun (hp : p) =>
        Or.intro_left (q ∧ r) hp)
      (fun (hr : r) =>
        Or.intro_right p ⟨hq, hr⟩))
    )


-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro

    (fun (h : p → (q → r)) =>
      fun (hpq : p ∧ q) => (h hpq.left) hpq.right
    )

    (fun (h : p ∧ q → r) =>
      fun (hp : p) =>
        fun (hq :q) => h ⟨hp, hq⟩
    )

#check And.intro
#check Or.elim

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun (h : (p ∨ q) → r) =>
      And.intro
        (fun (hp : p) => h (Or.intro_left q hp))
        (fun (hq : q) => h (Or.intro_right p hq))
      )

    (fun (h : (p → r) ∧ (q → r)) =>
      fun (h2 : p ∨ q) =>
        Or.elim h2
          (h.left)
          (h.right)
    )

#check And.intro
#check Or.elim

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun (h : ¬(p ∨ q)) =>
      And.intro
        (fun (hp : p) => h (Or.intro_left q hp))
        (fun (hq : q) => h (Or.intro_right p hq))
      )
    (fun (h : ¬p ∧ ¬q) =>
      fun (hpq : p ∨ q) =>
        Or.elim
          hpq
          (fun (hp : p) => h.left hp)
          (fun (hq : q) => h.right hq)
          )


example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun (h : ¬p ∨ ¬q) => Or.elim
    h
    (fun (hp : ¬p) => fun (hpq : p ∧ q) => hp hpq.left)
    (fun (hq : ¬q) => fun (hpq : p ∧ q) => hq hpq.right)



example : ¬(p ∧ ¬p) :=
fun (h : p ∧ ¬p) =>
  h.right h.left


example : p ∧ ¬q → ¬(p → q) :=
  fun (h : p ∧ ¬q) =>
    fun (h2 : p → q) =>
      h.right (h2 h.left)


#check False.elim

example : ¬p → (p → q) :=
  fun (h : ¬p) =>
    fun (hp : p) =>
      False.elim (h hp)

example : (¬p ∨ q) → (p → q) :=
  fun (h : ¬p ∨ q) =>
    Or.elim
      h
      (fun (hnp : ¬p) =>
        fun (hp : p) => False.elim (hnp hp))
      (fun (hq : q) =>
        fun (_ : p) => hq)

-- REM: underscore because the hypothesis hp would be useless!



example : p ∨ False ↔ p :=
  Iff.intro
    (fun (h : p ∨ False) =>
      Or.elim
        h
        (fun (hp : p) => hp)
        (fun (hfalse : False) => False.elim hfalse)
        )
    (fun (hp : p) =>
      Or.intro_left False hp)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun (h : p ∧ False) => h.right)
    (fun (hfalse : False) =>
      And.intro
        (False.elim hfalse)
        (hfalse)
        )


example : (p → q) → (¬q → ¬p) :=
  fun (h : p → q) =>
    fun (hnq : ¬q) =>
      fun (hp : p) => hnq (h hp)






end CHAPTER3
