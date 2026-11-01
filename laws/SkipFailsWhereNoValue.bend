# `skip` at a position where no value may start (before an object key, at a
# close bracket, after the root, or on a failed cursor) returns a failed
# cursor
#
# also rests on: laws/PullFailedSkip.bend
import Base
import ../main.bend as Ezjson
import ../src/pull.bend as Pull
import ./defs/CursorAndNumberRules.bend as D1

# LAW: skip after the root is the failed cursor
law pull_over_skip:
  for rest: String
  for stack: List<&2, Pull.Frame>
  for +bad: Bool
  {Ezjson.skip(Pull.Cur{rest, stack, True{}, bad}) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}

# LAW: skip before an object key, after any whitespace, is the failed cursor
law skip_key:
  for +ws: String
  for +key: String
  for fresh: Bool
  for stack: List<&2, Pull.Frame>
  for h_ws: {D1.all_ws(ws) == True{} : Bool}
  {Ezjson.skip(Pull.Cur{ws ++ SCon{'"', key}, Pull.FObj{Pull.SKey{}, fresh} <> stack, False{}, False{}})
    == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}

# LAW: skip at a close bracket, after any whitespace, is the failed cursor
law skip_close_arr:
  for +ws: String
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for h_ws: {D1.all_ws(ws) == True{} : Bool}
  {Ezjson.skip(Pull.Cur{ws ++ SCon{']', rest}, stack, False{}, False{}})
    == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}

# LAW: skip at a close brace, after any whitespace, is the failed cursor
law skip_close_obj:
  for +ws: String
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for h_ws: {D1.all_ws(ws) == True{} : Bool}
  {Ezjson.skip(Pull.Cur{ws ++ SCon{'}', rest}, stack, False{}, False{}})
    == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
