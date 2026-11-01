import Base
import ../main.bend as Ezjson
import ../src/pull.bend as Pull

# LAW: skip on a failed cursor is the failed cursor
law pull_failed_skip:
  for rest: String
  for stack: List<&2, Pull.Frame>
  for +done: Bool
  {Ezjson.skip(Pull.Cur{rest, stack, done, True{}}) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
