# For texts shorter than 2^32 - 1 characters: inserting any run of U+0020,
# U+0009, U+000A and U+000D before or after any token of a JSON text leaves
# `parse`'s result the same value; inserting any other character there, except
# a digit or `-` (which can make or extend a number), makes it `None` (§2)
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1
import ./defs/Digit.bend as D2
import ./defs/GrammarDerivations.bend as D3

# a derivation with its whitespace fields emptied: its tokens, without the
# whitespace §2 allows before and after them
def g.bare(gg: D3.Gv) -> D3.Gv:
  match gg:
    case D3.GWord{w}:
      D3.GWord{w}
    case D3.GStr{ps}:
      D3.GStr{ps}
    case D3.GArr0{_}:
      D3.GArr0{""}
    case D3.GArr{_, vv, _, rr}:
      D3.GArr{"", g.bare(vv), "", g.bare(rr)}
    case D3.GObj0{_}:
      D3.GObj0{""}
    case D3.GObj{_, ps, _, _, vv, _, rr}:
      D3.GObj{"", ps, "", "", g.bare(vv), "", g.bare(rr)}
    case D3.GEnd{}:
      D3.GEnd{}
    case D3.GNext{_, vv, _, rr}:
      D3.GNext{"", g.bare(vv), "", g.bare(rr)}
    case D3.GNextM{_, ps, _, _, vv, _, rr}:
      D3.GNextM{"", ps, "", "", g.bare(vv), "", g.bare(rr)}

# where a scan for the places between tokens is: outside strings, just after
# a word character or not; inside a string; or just after a backslash inside
# one (§7)
type Gp is Data:
  GpOut{wd: Bool}
  GpIn{}
  GpEsc{}

# one character of the scan
def gp.step(st: Gp, +ch: Char) -> Gp:
  match st:
    case GpOut{_}:
      Bool.pick(Gp, D1.is_cp(ch, 34), GpIn{}, GpOut{D1.word_char(ch)})
    case GpIn{}:
      Bool.pick(Gp, D1.is_cp(ch, 92), GpEsc{}, Bool.pick(Gp, D1.is_cp(ch, 34), GpOut{False{}}, GpIn{}))
    case GpEsc{}:
      GpIn{}

# the scan of every character, in order
def gp.run(txt: String, st: Gp) -> Gp:
  match txt:
    case SNil{}:
      st
    case SCon{hd, tl}:
      gp.run(tl, gp.step(st, hd))

# the text starts with a word character
def word_first(txt: String) -> Bool:
  match txt:
    case SNil{}:
      False{}
    case SCon{hd, _}:
      D1.word_char(hd)

# where the scan of the text before a place ended, the text after it given
def gap.at(st: Gp, post: String) -> Bool:
  match st:
    case GpOut{wd}:
      Bool.not(Bool.and(wd, word_first(post)))
    case GpIn{}:
      False{}
    case GpEsc{}:
      False{}

# whether the place between pre and post is before or after a token: outside
# strings, and not inside a word, with a word character on both sides. The
# places inside whitespace between two tokens count too
def gap(pre: String, post: String) -> Bool:
  gap.at(gp.run(pre, GpOut{False{}}), post)

# LAW: whitespace put before or after any token of a JSON text, or taken
# out, leaves parse's result the same value. The places before and after
# the tokens are the whitespace fields of the text's derivation, the first
# and last around the value (text_derives), so the two texts are two
# derivations with the same tokens (g.bare) and whitespace in every field
law ws_same:
  for +gg: D3.Gv
  for +hh: D3.Gv
  for +wa: String
  for +wb: String
  for +wc: String
  for +wd: String
  for +h_g: {D3.derived(wa, gg, wb) == True{} : Bool}
  for +h_h: {D3.derived(wc, hh, wd) == True{} : Bool}
  for +h_e: {g.bare(gg) == g.bare(hh) : D3.Gv}
  for h_sg: {D1.short(wa ++ D3.g.text(gg) ++ wb) == True{} : Bool}
  for h_sh: {D1.short(wc ++ D3.g.text(hh) ++ wd) == True{} : Bool}
  {D1.own_m(Ezjson.parse(wc ++ D3.g.text(hh) ++ wd)) == D1.own_m(Ezjson.parse(wa ++ D3.g.text(gg) ++ wb)) : Maybe<&2,
      V.Json>}

# LAW: any character but whitespace, a digit or `-` put before or after a
# token of a JSON text makes parse None. A place is before or after a token
# when it is outside strings and not inside a word (gap); a digit or `-` can
# make or extend a number there
law ins_none:
  for +pre: String
  for +post: String
  for +ch: Char
  for h_p: {D1.is_some(Ezjson.parse(pre ++ post)) == True{} : Bool}
  for h_g: {gap(pre, post) == True{} : Bool}
  for h_w: {D1.is_ws(ch) == False{} : Bool}
  for h_n: {Bool.or(D2.digit(ch), D1.is_cp(ch, 45)) == False{} : Bool}
  for h_s: {D1.short(pre ++ post) == True{} : Bool}
  for h_t: {D1.short(pre ++ SCon{ch, post}) == True{} : Bool}
  {Ezjson.parse(pre ++ SCon{ch, post}) == None{} : Maybe<&2, V.Json>}
