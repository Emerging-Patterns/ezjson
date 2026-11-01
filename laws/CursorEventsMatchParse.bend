# For every text `t` shorter than 2^32 characters, the events `next` yields
# from `cursor(t)` end in `EEnd` exactly when `parse(t)` is `Some{j}`, and
# then they are `events(j)`: the value's scalars, keys and container begins
# and ends in document order, with no event for a comma or a colon
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1

# LAW: the events next yields from the cursor of a text that parses are the
# value's events, then the end
law pull_events:
  for +txt: String
  for +jj: V.Json
  for +h_s: {D1.short(txt) == True{} : Bool}
  for +h_p: {Ezjson.parse(txt) == Some{jj} : Maybe<&2, V.Json>}
  {D1.pulled(1n+List.length(&2, D1.Evt, D1.events(jj)), Ezjson.cursor(txt)) == List.append(&2, D1.Evt, D1.events(jj),
      [D1.VEnd{}])
    : List<&2, D1.Evt>}

# LAW: the events next yields from a text's cursor reach the end only when
# the text parses
law pull_ends:
  for +txt: String
  for +kk: Nat
  for +h_s: {D1.short(txt) == True{} : Bool}
  for h_e: {D1.is_end(D1.ev_of(Ezjson.next(D1.nexts(kk, Ezjson.cursor(txt))))) == True{} : Bool}
  {D1.is_some(Ezjson.parse(txt)) == True{} : Bool}
