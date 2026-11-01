# Once `next` yields `EErr`, every later `next` on the returned cursor yields
# `EErr`, and `skip` returns a failed cursor
#
# also rests on: laws/PullFailedSkip.bend
import Base
import ../main.bend as Ezjson
import ../src/pull.bend as Pull
import ./defs/CursorAndNumberRules.bend as D1

# the error event
def is_err(ev: Pull.Ev) -> Bool:
  match ev:
    case Pull.EErr{}:
      True{}
    case _:
      False{}

# LAW: next on a failed cursor is an error and a failed cursor
law pull_failed_next:
  for rest: String
  for stack: List<&2, Pull.Frame>
  for done: Bool
  {Ezjson.next(Pull.Cur{rest, stack, done, True{}}) == (Pull.EErr{}, Pull.Cur{"", [], False{}, True{}})
    : (Pull.Ev & Pull.Cur)}

# LAW: an error from next comes with a failed cursor
law pull_err_fails:
  for +cur: Pull.Cur
  for h_err: {is_err(D1.ev_of(Ezjson.next(cur))) == True{} : Bool}
  {D1.failed(D1.cur_of(Ezjson.next(cur))) == True{} : Bool}
