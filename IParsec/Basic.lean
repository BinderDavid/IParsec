inductive IndentationRel : Type where
  | Eq : IndentationRel
  | Gt : IndentationRel
  | Ge : IndentationRel
  | Any : IndentationRel

def ParseError : Type := String

abbrev Indentation : Type := Int


def maxInd : Indentation := 1000

structure IndentationState : Type where
  min : Indentation
  max : Indentation
  absMode : Bool
  rel : IndentationRel

def initialIndentationState : IndentationState :=
  { min := 0, max := maxInd, absMode := False, rel := IndentationRel.Any}

structure State  : Type  where
  input : String
  indent : IndentationState

inductive Consumed (α : Type) : Type where
  | Consumed : α → Consumed α
  | Empty : α → Consumed α

inductive Reply (α : Type) : Type where
  | Ok : α → State → Reply α
  | Error : ParseError → Reply α

structure Parsec (α : Type) : Type where
  run : (State → Consumed (Reply α))

/--
Modify the state the parser is run in.
-/
def modifyState {α : Type}(f : State → State)(p : Parsec α) : Parsec α :=
  Parsec.mk (λ s => p.run (f s))

def parsec_bind {α β : Type} :
   Parsec α →
   (α -> Parsec β) →
   Parsec β :=
   open Reply in
   λ ma f => Parsec.mk (λ s =>
     match ma.run s with
     | Consumed.Consumed (Ok a s') => (f a).run s'
     | Consumed.Consumed (Error err) => (Consumed.Consumed (Error err))
     | Consumed.Empty (Ok a s') => (f a).run s'
     | Consumed.Empty (Error err) => Consumed.Empty (Error err)
     )

instance parsecMonad : Monad Parsec where
  pure := λ x => Parsec.mk (λ s => Consumed.Empty (Reply.Ok x s))
  bind := parsec_bind

/--
Sets the indentation relation for the next token.
Corresponds to `p^rel` in the paper.
-/
def localIndentation {α : Type}(rel : IndentationRel)(p : Parsec α) : Parsec α := sorry

/--
Corresponds to `|p|` in the paper.
-/
def absoluteIndentation {α : Type}(p : Parsec α) : Parsec α := sorry

/--
Sets the default indentation mode that is applied to all tokens to the given indentation relation.
-/
def localTokenMode {α : Type}(rel : IndentationRel)(p : Parsec α) : Parsec α :=
  modifyState (λ ⟨input, indents⟩ => State.mk input {indents with  rel := rel }) p

def charP (c : Char) : Parsec Unit :=
  Parsec.mk (λ s => match s.input.toList with
                    | List.nil => Consumed.Empty (Reply.Error "input is empty")
                    | List.cons x xs => if x == c
                                        then Consumed.Consumed (Reply.Ok Unit.unit ⟨String.mk xs, s.indent⟩)
                                        else Consumed.Consumed (Reply.Error "Character doesn't match")
                    )


def parse{α : Type} (input : String) (parser : Parsec α) : Option α :=
  let initialState : State := { input := input, indent := initialIndentationState }
  match parser.run initialState with
  | Consumed.Consumed (Reply.Ok res _) => some res
  | Consumed.Empty (Reply.Ok res _) => some res
  | _ => none

def backtrack{α : Type}(p : Parsec α) : Parsec α :=
  Parsec.mk (λ s => match p.run s with
                    | Consumed.Consumed (Reply.Ok res s') => Consumed.Consumed (Reply.Ok res s')
                    | Consumed.Consumed (Reply.Error err) => Consumed.Empty (Reply.Error err)
                    | Consumed.Empty (Reply.Ok res s') => Consumed.Empty (Reply.Ok res s')
                    | Consumed.Empty (Reply.Error err) => Consumed.Empty (Reply.Error err)
                    )

/--
A parser that immediately fails without consuming any input.
-/
def fail {α : Type} : Parsec α :=
  Parsec.mk (λ _ => Consumed.Empty (Reply.Error "fail"))

/-- Left-biased or-combinator which doesn't backtrack -/
def or {α: Type}(p₁ p₂ : Parsec α): Parsec α :=
  Parsec.mk (λ s => match p₁.run s with
                    | Consumed.Consumed (Reply.Ok res s') => Consumed.Consumed (Reply.Ok res s')
                    | Consumed.Consumed (Reply.Error err) => Consumed.Consumed (Reply.Error err)
                    | Consumed.Empty (Reply.Ok res s') => Consumed.Empty (Reply.Ok res s')
                    | Consumed.Empty (Reply.Error _) => p₂.run s
  )

def ors{α : Type}(ps : List (Parsec α)) : Parsec α :=
  List.foldr or fail ps


def aab_parser : Parsec Unit := do
  charP 'a'
  charP 'a'
  charP 'b'

def a_or_b_parser : Parsec Unit := or (backtrack (charP 'a')) (charP 'b')

#guard parse "" (charP 'a') == none
#guard parse "a" (charP 'a') == some Unit.unit
#guard parse "b" (charP 'a') == none
#guard parse "aab" aab_parser == some Unit.unit
#guard parse "bba" aab_parser == none
#guard parse "a" a_or_b_parser == some Unit.unit
#guard parse "b" a_or_b_parser == some Unit.unit
