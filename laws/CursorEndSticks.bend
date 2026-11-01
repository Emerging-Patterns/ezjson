# Once `next` yields `EEnd`, every later `next` on the returned cursor yields
# `EEnd`
import Base
import ../main.bend as Ezjson
import ../src/pull.bend as Pull
import ./defs/CursorAndNumberRules.bend as D1

# LAW: an end from next comes with an ended cursor
law pull_end_ends:
  for +cur: Pull.Cur
  for h_end: {D1.is_end(D1.ev_of(Ezjson.next(cur))) == True{} : Bool}
  {D1.ended(D1.cur_of(Ezjson.next(cur))) == True{} : Bool}

# LAW: next on an ended cursor is the end and the same ended cursor
law pull_ended_next:
  for stack: List<&2, Pull.Frame>
  {Ezjson.next(Pull.Cur{"", stack, True{}, False{}}) == (Pull.EEnd{}, Pull.Cur{"", stack, True{}, False{}})
    : (Pull.Ev & Pull.Cur)}
