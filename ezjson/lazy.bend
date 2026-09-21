# ezjson/lazy: a branch that does not run both ways. `stop` takes `a` when
# c, else what rest gives, so a search can return without walking the rest.
import Base

# `a` when c, else what rest gives: the early exit of a search
def stop(-A: Type, c: Bool, a: A, rest: Unit -> A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      rest(Unit{})
