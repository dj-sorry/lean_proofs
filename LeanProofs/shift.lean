import Mathlib.Data.String.Basic

-- Basic types
structure Entity where
  name : String
deriving BEq, Repr

-- Semantic types
def IntransitiveVerb : Type := Entity → Prop
def TransitiveVerb : Type := Entity → Entity → Prop
def NounPhrase : Type := (Entity → Prop) → Prop

-- Sample predicates and entities
def sleep : IntransitiveVerb :=
  fun x => x.name = "John" ∨ x.name = "Mary"

def like : TransitiveVerb :=
  fun x y => (x.name = "John" ∧ y.name = "Mary") ∨ (x.name = "Mary" ∧ y.name = "John")

def some_human : NounPhrase :=
  fun scope => ∃ x, (x.name = "John" ∨ x.name = "Mary") ∧ scope x

def shift_TV_to_IV (tv : TransitiveVerb) (obj : Entity) : IntransitiveVerb :=
  fun subj => tv subj obj

def shift_NP_to_TV_obj (np : NounPhrase) (tv : TransitiveVerb) : IntransitiveVerb :=
  fun subj => np (fun obj => tv subj obj)

def john : Entity := { name := "John" }
def mary : Entity := { name := "Mary" }

theorem some_human_likes_mary :
  some_human (shift_TV_to_IV like mary) :=
  Exists.intro john (And.intro (Or.inl rfl) (Or.inl (And.intro rfl rfl)))

theorem some_human_likes_someone :
  some_human (shift_NP_to_TV_obj some_human like) :=
  Exists.intro john (
    And.intro (Or.inl rfl) (
      Exists.intro mary (
        And.intro (Or.inr rfl) (Or.inl (And.intro rfl rfl))
      )
    )
  )

theorem cant_prove_no_human_likes_self :
  ¬(∀ x, (x.name = "John" ∨ x.name = "Mary") → ¬(like x x)) :=
fun h =>
  let john_likes_self := h john (Or.inl rfl)
  john_likes_self (Or.inr (And.intro rfl rfl))

#check some_human_likes_mary
#check some_human_likes_someone
#check cant_prove_no_human_likes_self
