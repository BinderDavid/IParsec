import Veriflex.Located
open Veriflex

inductive IndentationRel : Type where
  | Eq : IndentationRel
  | Gt : IndentationRel
  | Ge : IndentationRel
  | Any : IndentationRel

def ParseError : Type := String

abbrev Indentation : Type := Nat

def maxInd : Indentation := 1000

structure IndentationState : Type where
  min : Indentation
  max : Indentation
  absMode : Bool
  rel : IndentationRel

def initialIndentationState : IndentationState :=
  { min := 0, max := maxInd, absMode := False, rel := IndentationRel.Any}

structure State(tok : Type) : Type  where
  input : List (Located tok)
  indent : IndentationState

inductive Consumed (α : Type) : Type where
  | Consumed : α → Consumed α
  | Empty : α → Consumed α

inductive Reply (tok α : Type) : Type where
  | Ok : α → State tok → Reply tok α
  | Error : ParseError → Reply tok α

structure Parsec (tok α : Type) : Type where
  run : (State tok → Consumed (Reply tok α))

/--
Modify the state the parser is run in.
-/
def modifyState {tok α : Type}(f : State tok → State tok)(p : Parsec tok α) : Parsec tok α :=
  Parsec.mk (λ s => p.run (f s))

def parsec_bind {tok α β : Type} :
   Parsec tok α →
   (α -> Parsec tok β) →
   Parsec tok β :=
   open Reply in
   λ ma f => Parsec.mk (λ s =>
     match ma.run s with
     | Consumed.Consumed (Ok a s') => (f a).run s'
     | Consumed.Consumed (Error err) => (Consumed.Consumed (Error err))
     | Consumed.Empty (Ok a s') => (f a).run s'
     | Consumed.Empty (Error err) => Consumed.Empty (Error err)
     )

instance parsecMonad {tok : Type} : Monad (Parsec tok) where
  pure := λ x => Parsec.mk (λ s => Consumed.Empty (Reply.Ok x s))
  bind := parsec_bind

/--
Sets the indentation relation for the next token.
Corresponds to `p^rel` in the paper.
-/
def localIndentation {tok α : Type}(rel : IndentationRel)(p : Parsec tok α) : Parsec tok α := sorry

/--
Corresponds to `|p|` in the paper.
-/
def absoluteIndentation {tok α : Type}(p : Parsec tok α) : Parsec tok α := sorry

/--
Sets the default indentation mode that is applied to all tokens to the given indentation relation.
-/
def localTokenMode {tok α : Type}(rel : IndentationRel)(p : Parsec tok α) : Parsec tok α :=
  modifyState (λ ⟨input, indents⟩ => State.mk input {indents with  rel := rel }) p

/--
Parse a single token.
-/
def tokenP{tok : Type}[BEq tok](c : tok) : Parsec tok Unit :=
  Parsec.mk (λ s => match s.input with
                    | List.nil => Consumed.Empty (Reply.Error "Input is empty")
                    | List.cons x xs => if x.content == c
                                        then Consumed.Consumed (Reply.Ok Unit.unit ⟨xs, s.indent⟩)
                                        else Consumed.Consumed (Reply.Error "Character doesn't match")
                    )

/--
Parses and returns a single token if it satisfies the given predicate.
-/
def satisfyP{tok : Type}(p : tok → Bool) : Parsec tok tok :=
  Parsec.mk (λ s => match s.input with
                    | List.nil => Consumed.Empty (Reply.Error "Input is empty")
                    | List.cons x xs => if p x.content
                                        then Consumed.Consumed (Reply.Ok x.content ⟨xs, s.indent⟩)
                                        else Consumed.Consumed (Reply.Error "Token does not satisfy predicate."))


def parse{α : Type} (input : String) (parser : Parsec Char α) : Option α :=
  let initialState : State Char := { input := input.toList.map (λ x => ⟨0,x⟩), indent := initialIndentationState }
  match parser.run initialState with
  | Consumed.Consumed (Reply.Ok res _) => some res
  | Consumed.Empty (Reply.Ok res _) => some res
  | _ => none

def backtrack{tok α : Type}(p : Parsec tok α) : Parsec tok α :=
  Parsec.mk (λ s => match p.run s with
                    | Consumed.Consumed (Reply.Ok res s') => Consumed.Consumed (Reply.Ok res s')
                    | Consumed.Consumed (Reply.Error err) => Consumed.Empty (Reply.Error err)
                    | Consumed.Empty (Reply.Ok res s') => Consumed.Empty (Reply.Ok res s')
                    | Consumed.Empty (Reply.Error err) => Consumed.Empty (Reply.Error err)
                    )

/--
A parser that immediately fails without consuming any input.
-/
def fail {tok α : Type} : Parsec tok α :=
  Parsec.mk (λ _ => Consumed.Empty (Reply.Error "fail"))

/-- Left-biased or-combinator which doesn't backtrack -/
def or {tok α: Type}(p₁ p₂ : Parsec tok α): Parsec tok α :=
  Parsec.mk (λ s => match p₁.run s with
                    | Consumed.Consumed (Reply.Ok res s') => Consumed.Consumed (Reply.Ok res s')
                    | Consumed.Consumed (Reply.Error err) => Consumed.Consumed (Reply.Error err)
                    | Consumed.Empty (Reply.Ok res s') => Consumed.Empty (Reply.Ok res s')
                    | Consumed.Empty (Reply.Error _) => p₂.run s
  )

def ors{tok α : Type}(ps : List (Parsec tok α)) : Parsec tok α :=
  List.foldr or fail ps


partial def many{tok α : Type}(p : Parsec tok α) : Parsec tok (List α) :=
  let f : Parsec tok (List α) := do
    let x ← p
    let xs ← many p
    pure (x :: xs)
  or f (pure [])

def many1{α : Type}(p : Parsec tok α) : Parsec tok (List α) := do
  let x ← p
  let xs ← many p
  pure (x :: xs)

def aab_parser : Parsec Char Unit := do
  tokenP 'a'
  tokenP 'a'
  tokenP 'b'

def a_or_b_parser : Parsec Char Unit := or (backtrack (tokenP 'a')) (tokenP 'b')


#guard parse "" (tokenP 'a') == none
#guard parse "a" (tokenP 'a') == some Unit.unit
#guard parse "b" (tokenP 'a') == none
#guard parse "aab" aab_parser == some Unit.unit
#guard parse "bba" aab_parser == none
#guard parse "a" a_or_b_parser == some Unit.unit
#guard parse "b" a_or_b_parser == some Unit.unit
#guard parse "" (many (tokenP 'a')) == some []
#guard parse "aa" (many (tokenP 'a')) == some [Unit.unit, Unit.unit]
#guard parse "" (many1 (tokenP 'a')) == none
#guard parse "aa" (many1 (tokenP 'a')) == some [Unit.unit, Unit.unit]
