import Simpl.Syntax
import Std
import Lean

namespace Simpl

abbrev Record := Std.HashMap
abbrev CVal := UInt32
instance : Repr $ Record Lean.Name CVal where
  reprPrec r prec := reprPrec (r.toList) prec

inductive Status where
  | Normal : Status
  | Abrupt : Status
  | Stuck : Status
  | Fault : Status

  deriving Inhabited, Repr
structure State where
  (local_variables : Record Lean.Name CVal)
  (global_variables : Record Lean.Name CVal)
  deriving Inhabited, Repr

/-
  The main reason why we build our own syntax types, instead of using the Lean ones (i.e. TSyntax `nonterminal) is that we can't build new syntax terms without going into some monad (like Lean.MonadQuotation). See for example what happens with:
```
#check `(expression| 1 + 2)
```
yields:
```
do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let scp ← Lean.getCurrMacroScope
  let mainModule ← Lean.getMainModule
  pure
      {
        raw :=
          Lean.Syntax.node3 info `Simpl.expression_+_
            (Lean.Syntax.node1 info `Simpl.expression_ (Lean.Syntax.node1 info `num (Lean.Syntax.atom info "1")))
            (Lean.Syntax.atom info "+")
            (Lean.Syntax.node1 info `Simpl.expression_
              (Lean.Syntax.node1 info `num (Lean.Syntax.atom info "2"))) } : ?m.876 (Lean.TSyntax `expression)
```

We can't thus define eval recursively by just saying
```
  `(expression| $i + $j) => eval `(expression| $i) + eval `(expression| $j)
```
because we can't build the new syntax terms for recursive functions, like so:

mutual
def eval  : State → (Lean.TSyntax `statement) → State
  | state, Statement.skip => state
  | state, `(statement| $i:ident :== $e) =>
    let new_local_variables := state.local_variables.insert i (eval_expr state e)
    { state with local_variables := new_local_variables }
  | state, `(statement| SKIP) => state
  | state, _ => state

def eval_expr : State → (Lean.TSyntax `expr) → CVal
  | state, `(expression| $i:ident) => state.local_variables.findD i.getId 0
  | state, `(expression| $n:num) => n.getNat.toUInt32
  | state, _ => 0
end

-/

mutual
-- eval won't work as function without coinduction
def SmallStep : State × Statement → State × Statement
  | (state, Statement.skip) => (state, Statement.skip)
  | (state, Statement.assign i e) =>
    let new_local_variables := state.local_variables.insert i (eval_expr state e)
    ({ state with local_variables := new_local_variables }, Statement.skip)
  | (state, Statement.seq (Statement.skip) s₂) => step (state,s₂)
  | (state, Statement.seq s₁ s₂) => match step (state,s₁) with
    | (state', Statement.skip) => (state',s₂)
    | (state', s₁') => (state', Statement.seq s₁' s₂)
  | (state, Statement.conditional e s₁ s₂) =>
    if eval_expr state e ≠ 0 then step (state, s₁) else step (state, s₂)
  | (state, w@(Statement.while e s)) =>
    if eval_expr state e ≠ 0 then (state, Statement.seq s w) else (state, Statement.skip)
  | s@(_, Statement.throw _) => s
  | (state, Statement.trycatch t c) => match step (state,t) with
    | (state', Statement.skip) => (state', Statement.skip)
    | (state', Statement.throw e) => step (state', Statement.seq (Statement.assign `exception e) c)
    | (state', t') => (state', t)
  | (state, Statement.guard e₁ e₂ s₁) => (state, Statement.skip) -- TODO: implement
  | (state, Statement.call _) => (state, Statement.skip) -- TODO: implement

 def eval_expr : State → Expression → CVal
  | state, Expression.ident i => state.local_variables.findD i 0
  | _, Expression.num n => n.toUInt32
  | state, Expression.add e₁ e₂ => eval_expr state e₁ + eval_expr state e₂
  | state, Expression.sub e₁ e₂ => eval_expr state e₁ - eval_expr state e₂
end

partial def eval (s : Statement) (state : State := default) : State :=
  match step (state, s) with
    | (state', Statement.skip) => state'
    | (state', s') => eval s' state'

def test := [simpl|
  X :== 10;
  Y :== 1;
  WHILE X DO
    X :== X - 1;
    Y :== Y + Y
  OD
]

#eval eval test
end Simpl
