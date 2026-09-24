# src/lazy: `stop` returns `val` when `cond` holds, and otherwise calls rest.
import Base

# `val` when `cond`, else what rest gives: the early exit of a search
def stop(-A: Type, cond: Bool, val: A, rest: Unit -> A) -> A:
  match cond:
    case True{}:
      val
    case False{}:
      rest(Unit{})
