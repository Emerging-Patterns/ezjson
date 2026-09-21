# ezjson/lazy: `stop` returns `a` when c holds, and otherwise calls rest.
import Base

# `a` when c, else what rest gives: the early exit of a search
def stop(-A: Type, c: Bool, a: A, rest: Unit -> A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      rest(Unit{})
