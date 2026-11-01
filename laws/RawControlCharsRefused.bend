# For texts shorter than 2^32 - 1 characters: inside a string, a raw U+0000 to
# U+001F makes `parse` `None`, and every other raw code point except `"` and
# `\` is kept as itself (§7)
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/fixed.bend as F
import ./defs/CursorAndNumberRules.bend as D1

# where a scan for raw controls in strings is: outside strings, inside one,
# just after a backslash inside one, or past a raw control inside one (§7)
type Cs is Data:
  CsOut{}
  CsIn{}
  CsEsc{}
  CsHit{}

# one character of the scan
def cs.step(st: Cs, +ch: Char) -> Cs:
  match st:
    case CsOut{}:
      Bool.pick(Cs, D1.is_cp(ch, 34), CsIn{}, CsOut{})
    case CsIn{}:
      Bool.pick(Cs, D1.is_cp(ch, 34), CsOut{}, Bool.pick(Cs, D1.is_cp(ch, 92), CsEsc{}, Bool.pick(Cs,
        U32.is_lt(Char.to_u32(ch), 32), CsHit{}, CsIn{})))
    case CsEsc{}:
      CsIn{}
    case CsHit{}:
      CsHit{}

# the scan of every character, in order
def cs.run(cs: List<&2, Char>, st: Cs) -> Cs:
  match cs:
    case Nil{}:
      st
    case Con{hd, tl}:
      cs.run(tl, cs.step(st, hd))

# whether a scan met a raw control inside a string
def cs.hit(st: Cs) -> Bool:
  match st:
    case CsHit{}:
      True{}
    case _:
      False{}

# whether a text holds a raw control U+0000 to U+001F inside a string
def raw_ctl(txt: String) -> Bool:
  cs.hit(cs.run(String.to_list(txt), CsOut{}))

# LAW: inside a string, a raw character other than a control, a quotation
# mark or a reverse solidus is kept as itself
law raw_kept:
  for +txt: String
  for h_r: {D1.raw_ok(String.to_list(txt)) == True{} : Bool}
  for h_s: {D1.short("\"" ++ txt ++ "\"") == True{} : Bool}
  {D1.str_of(Ezjson.parse("\"" ++ txt ++ "\"")) == Some{txt} : Maybe<&2, String>}

# LAW: a raw control U+0000 to U+001F inside a string makes parse None
law ctl_none:
  for +txt: String
  for h_c: {raw_ctl(txt) == True{} : Bool}
  for h_s: {D1.short(txt) == True{} : Bool}
  {Ezjson.parse(txt) == None{} : Maybe<&2, V.Json>}
